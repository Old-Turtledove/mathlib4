#!/usr/bin/env bash

 : <<'DOC_MODULE'
This file contains code to compute certain "global" statistics of Mathlib.

The information is typically posted to Zulip in
[#mathlib4 "Mathlib weekly change report"](https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Mathlib.20weekly.20change.20report).

The main discussion for these statistics is [this thread](https://leanprover.zulipchat.com/#narrow/stream/113488-general).

Further suggestions of possible statistics are

* Top five popular tactics since last post
* Net change in number of lines of Mathlib
* Number of new declarations
* Number of invisible (autogenerated) declarations
* Number of docstrings
* Percentage of documented declarations (possibly split by type)
* Longest proof (expression)
* Longest proof (syntax)
* Most popular starting tactic
* Most popular finishing tactic
* New modules with docstrings
* Longest pole
* Slowest proofs
* Slowest files
* Number of instances
* Number of simp lemmas
* Number of classes
* Number of linters
* Number of environment extensions

DOC_MODULE

statsURL="https://leanprover-community.github.io/mathlib_stats.html"
mlURL="https://github.com/leanprover-community/mathlib4"

## results in 'hash YYYY-MM-DD'
hashAndDate="$(git log master --since='one week ago' --date=short --pretty="%H %ad" | tail -1)"

## just the commit hash
oldCommit="${hashAndDate/% */}"
oldCommitURL="[${oldCommit:0:10}](${mlURL}/commit/${oldCommit})"

currentCommit="$(git rev-parse HEAD)"
currentCommitURL="[${currentCommit:0:10}](${mlURL}/commit/${currentCommit})"
## just the date
date=${hashAndDate/#* /}

#####################
# Git-based reports #
#####################

gcompare="${mlURL}/compare/${oldCommit}...${currentCommit}"

printf -v today '%(%Y-%m-%d)T\n' -1

# produce output `(+X -Y ~Z)` for the files added (+), deleted (-), modified (~)
filesPlusMinus="$(git diff --name-status "${oldCommit}"..."${currentCommit}" |
  awk '/^A/ { added++ }
       /^M/ { modified++}
       /^D/ {deleted++} END{
        printf("(+%d -%d ~%d)\n", added, deleted, modified)
  }')"

# `shortstat`: 'x files changed, y insertions(+), z deletions(-)'
# we extract `nums=[x, y, z]` and print
# `x files changed (+A -D ~M), y-z lines changed (+y -z)`
net=$(git diff --shortstat "${oldCommit}"..."${currentCommit}" |
  awk -v filesPlusMinus="${filesPlusMinus}" 'BEGIN{ con=0 }{
  for(i=1; i<=NF; i++) {
    if($i+0 == $i){ con++; nums[con]=$i } ## nums= [files changed, insertions, deletions]
  }
  if(con != 3) { print "Expected 3 fields from `git diff`" }
  printf("%s files changed %s, %s lines changed (+%s -%s)\n",
     nums[1],  filesPlusMinus, nums[2]-nums[3],  nums[2], nums[3]) }')

######################
# Lean-based reports #
######################

# produces a string of the form
# ```
# Theorems
# <one_decl_name_per_row>,
# ...
# Predicates
# <one_decl_name_per_row>,
# ...
# ```
getCountDecls () {
  sed 's=^--\(count_decls\)=\1=' scripts/count_decls.lean | lake env lean --stdin
}

# `tallyCountDecls file` extracts from `file`
# Theorems xx
# Predicates yy
# ...
tallyCountDecls () {
              # `count` is the index of the various `kind`s -- the fields of `Tally`
  awk 'BEGIN{ count=0 }
    # lines that do not end in `,` represent kinds and we accumulate them in `kind`
    # we also start a tally of them in `acc[count]`
    /[^,]$/ { count++; kind[count]=$0; acc[count]=0; }
    # lines that end in `,` represent declarations to be tallied
    /,$/ { acc[count]++ } END{
    for(t=1; t<=count; t++) { printf("%s %s\n", kind[t], acc[t]) }
  }' "${1}"
}

# `getKind kind file` extracts all declaration names of kind `kind` from `file`
getKind () {
  awk -v typ="${1}$" 'BEGIN{ found=0 }
      /[^,]$/ { found=0 }
      (found == 1) { print $0 }
      ($0 ~ typ) { found=1 }' "${2}" | sort
}

# the output of `count_decls`
newDeclsTots="$(getCountDecls)"

# the tally of the output of `count_decls`
newDecls="$(echo "${newDeclsTots}" | tallyCountDecls -)"
# Theorems 73590...
git checkout -q "${oldCommit}"
# 'detached HEAD' state

lake exe cache get > /dev/null
# stuff gets downloaded

# just in case some part of the cache is corrupted
lake build --quiet

# update the `count_decls` and `mathlib_stats` scripts to the latest version
git checkout -q origin/adomani/weekly_change_report scripts/count_decls.lean scripts/mathlib_stats.sh

# the output of `count_decls`
oldDeclsTots="$(getCountDecls)"

# the tally of the output of `count_decls`
oldDecls="$(echo "${oldDeclsTots}" | tallyCountDecls -)"
# Theorems 73152...

# produce the `+X -Y` report for the declarations in each category
plusMinus="$(for typ in $(echo "$newDeclsTots" | grep "[^,]$" | tr '\n' ' ');
do
  comm -123 --total <(
    echo "${newDeclsTots}" | getKind "${typ}$" -)  <(
    echo "${oldDeclsTots}" | getKind "${typ}$" -)
done)"

# produces the table summary of the declarations split by kind
declSummary="$(paste -d' ' <(echo "${newDecls}") <(echo "${oldDecls}") <(echo "${plusMinus}") |
  LC_ALL=en_US.UTF-8 awk 'BEGIN{ print "|Type|Total|%|\n|:-:|:-:|:-:|" }{
    printf("| %s | %'"'"'d (+%'"'"'d -%'"'"'d) | %4.2f%% |\n", $1, $2, $5, $6, ($2-$4)*100/$2)
  }'
)"

## final report
printf -- '---\n\n## Weekly stats ([%s...%(%Y-%m-%d)T](%s))\n\n' "${date}" -1 "${gcompare}"

printf -- '%s\n\n' "${declSummary}"

printf -- '%s\n\n' "${net}"

printf -- 'Reference commits: old %s, new %s.\n\n' "${oldCommitURL}" "${currentCommitURL}"

printf -- 'Take also a look at the [`Mathlib` stats page](%s).\n' "${statsURL}"
