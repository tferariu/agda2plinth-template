#!/usr/bin/env bash
#
# strip_lagda_newcommands.sh
#
# Finds and removes blocks of the form:
#
#     \end{code}
#     }
#     <any number of lines>
#     \newcommand\<randomString>{%
#     \begin{code}
#
# as well as blocks of the form:
#
#     \end{code}
#     }
#     <any number of lines>
#     \begin{code}
#
# from one or more .lagda files, editing them in place. Both forms share
# the same underlying shape - \end{code}, a line containing only "}", any
# number of lines of arbitrary content, then the next \begin{code} - so a
# single scan handles both: whatever sits between the "}" line and the
# next \begin{code} (whether that's a \newcommand line, blank lines, or
# anything else) is removed along with the \end{code}/}/\begin{code}
# lines themselves.
#
# Pure Bash - no perl/python/awk/sed required, just Bash builtins.
#
# Usage:
#   ./strip_lagda_newcommands.sh FILE.lagda [FILE2.lagda ...]
#
# Options:
#   --dry-run     Report matches without modifying any files
#   --no-backup   Don't write a FILE.lagda.bak backup before editing in place
#   -h, --help    Show this help
#
set -euo pipefail

# Patterns (ERE). A double backslash in a single-quoted string is a literal
# backslash character, which matches one '\' in the file.
end_code_re='^\\end\{code\}[[:space:]]*$'
close_brace_re='^\}[[:space:]]*$'
begin_code_re='^\\begin\{code\}[[:space:]]*$'

dry_run=0
make_backup=1
files=()

usage() {
    sed -n '2,29p' "$0" | sed 's/^# \{0,1\}//'
}

for arg in "$@"; do
    case "$arg" in
        --dry-run) dry_run=1 ;;
        --no-backup) make_backup=0 ;;
        -h|--help) usage; exit 0 ;;
        --) shift ;;
        -*)
            echo "Unknown option: $arg" >&2
            exit 1
            ;;
        *) files+=("$arg") ;;
    esac
done

if [[ ${#files[@]} -eq 0 ]]; then
    echo "Usage: $0 [--dry-run] [--no-backup] FILE.lagda [FILE2.lagda ...]" >&2
    exit 1
fi

total_matches=0

for file in "${files[@]}"; do
    if [[ ! -f "$file" ]]; then
        echo "Skipping $file: file not found" >&2
        continue
    fi

    mapfile -t lines < "$file"
    n=${#lines[@]}
    out=()
    i=0
    match_count=0

    while (( i < n )); do
        line="${lines[i]}"

        if [[ "$line" =~ $end_code_re ]] && (( i + 1 < n )) && [[ "${lines[i+1]}" =~ $close_brace_re ]]; then
            # Scan forward for the next \begin{code}; everything in
            # between (including a possible \newcommand line, or nothing
            # at all) is arbitrary content that gets removed too.
            j=$((i + 2))
            found=-1
            while (( j < n )); do
                if [[ "${lines[j]}" =~ $begin_code_re ]]; then
                    found=$j
                    break
                fi
                j=$((j + 1))
            done

            if (( found != -1 )); then
                match_count=$((match_count + 1))
                i=$((found + 1))
                continue
            fi
        fi

        out+=("$line")
        i=$((i + 1))
    done

    total_matches=$((total_matches + match_count))

    if (( match_count == 0 )); then
        echo "$file: no matches found"
        continue
    fi

    if (( dry_run == 1 )); then
        echo "$file: $match_count match(es) found (dry run, no changes written)"
        continue
    fi

    if (( make_backup == 1 )); then
        cp "$file" "$file.bak"
    fi

    tmpfile=$(mktemp "${file}.XXXXXX")
    printf '%s\n' "${out[@]}" > "$tmpfile"
    mv "$tmpfile" "$file"

    if (( make_backup == 1 )); then
        echo "$file: removed $match_count match(es) (backup saved to $(basename "$file").bak)"
    else
        echo "$file: removed $match_count match(es)"
    fi
done

echo ""
if (( dry_run == 1 )); then
    echo "Total matches found: $total_matches"
else
    echo "Total matches removed: $total_matches"
fi
