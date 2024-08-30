/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Cli.Basic
import Batteries.Data.HashMap

def validate_title(title: String) : IO UInt32 := do
  -- The title should be of the form "abbrev: main title" or "abbrev(scope): main title".
  let parts := title.splitOn ":"
  if parts.length < 2 then
    IO.println "error: the PR title does not contains a colon"
    return 1
  let mut numberErrors : UInt32 := 0
  let main := parts[1]!
  if main.endsWith "." then
    IO.println "error: the PR title should not end with a full stop"
    numberErrors := numberErrors + 1
  if main.front != ' ' then
    IO.println "error: the PR should have the form 'abbrev: main title', with a space"
    numberErrors := numberErrors + 1
  let main := main.removeLeadingSpaces
  if main.front.toLower != main.front then
    IO.println "error: the main PR title should be lowercased"
    numberErrors := numberErrors + 1

  let kind := parts[0]!
  let parts := kind.splitOn "("
  if parts.length >= 2 then
    if !kind.contains ')' then
      IO.println "error: the PR kind should be of the form abbrev or abbrev(scope)"
      numberErrors := numberErrors + 1
  else if kind.contains ')' then
    IO.println "error: the PR kind should be of the form abbrev or abbrev(scope)"
    numberErrors := numberErrors + 1

  let known_kinds := ["feat", "chore", "perf", "refactor", "style", "fix", "doc"]
  if !known_kinds.contains (parts.get! 0) then
    IO.println s!"error: the PR kind should be one of {", ".intercalate (known_kinds.map (s!"\"{·}\""))}"
    numberErrors := numberErrors + 1
  return numberErrors


def has_contradictory_labels(labels : List String) : Bool := Id.run do
  -- Combine common labels.
  let substitutions := [
    ("ready-to-merge", "bors"), ("auto-merge-after-CI", "bors"),
    ("blocked-by-other-PR", "blocked"), ("blocked-by-core-PR", "blocked"),
    ("blocked-by-batt-PR", "blocked"), ("blocked-by-qq-PR", "blocked"),
  ]
  let mut canonicalise : Lean.HashMap String String := .ofList substitutions
  let normalised_labels := labels.map fun label ↦ (canonicalise.findD label label)
  -- Test for contradictory label combinations.
  if normalised_labels.contains "awaiting-review-DONT-USE" then
    return true
  -- Waiting for a decision contradicts most other labels.
  else if normalised_labels.contains "awaiting-zulip" && ["awaiting-author", "delegated", "bors", "WIP"].any normalised_labels.contains then
    return true
  else if normalised_labels.contains "WIP" && ["awaiting-review", "bors"].any normalised_labels.contains then
    return true
  else if ["awaiting-author", "awaiting-zulip"].all normalised_labels.contains then
    return true
  else if ["bors", "WIP"].all normalised_labels.contains then
    return true
  else
    return false


open Cli in
/-- Implementation of the `mk_all` command line program.
The exit code is the number of files that the command updates/creates. -/
def checkTitleLabelCLI (args : Parsed) : IO UInt32 := do
  let title := (args.positionalArg! "title").value
  let labels : String := (args.positionalArg! "labels").value
  let labels := labels.splitOn " "
  let mut numberErrors := 0
  if !labels.contains "WIP" then
    -- We do not complain about WIP PRs.
    -- The title should be of the form "abbrev: main title" or "abbrev(scope): main title".
    numberErrors := ← validate_title title
    -- A feature PR should have a topic label.
    if title.startsWith "feat" && !labels.any (fun s ↦ s == "CI" || s.startsWith "t-") then
      IO.println "error: feature PRs should have a 't-something' or the 'CI' label"
      numberErrors := numberErrors + 1
  -- Check for contradictory labels.
  if has_contradictory_labels labels then
    IO.println "error: PR labels are contradictory"
    numberErrors := numberErrors + 1
  return numberErrors

open Cli in
/-- Setting up command line options and help text for `lake exe check-title-label`. -/
def checkTitleLabel : Cmd := `[Cli|
  «check-title-label» VIA checkTitleLabelCLI; ["0.0.1"]
  "Check that a PR title matches the formatting requirements.
  If this PR is a feature PR, also verify that it has a topic label."

  ARGS:
    title : String; "this PR's title"
    labels : String; "space-separated list of label names of this PR"
]

/-- The entrypoint to the `lake exe check-title-label` command. -/
def main (args : List String) : IO UInt32 := checkTitleLabel.validate args
