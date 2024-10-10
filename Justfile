# batteries
batteries_name := "batteries"
batteries_github := "https://github.com/leanprover-community/batteries"
batteries_rev := "daf1ed91789811cf6bbb7bf2f4dad6b3bad8fbf4"
# Qq
qq_name := "Qq"
qq_github := "https://github.com/leanprover-community/quote4"
qq_rev := "2b2f6d7fbe9d917fc010e9054c1ce11774c9088b"
# aesop
aesop_name := "aesop"
aesop_github := "https://github.com/leanprover-community/aesop"
aesop_rev := "b20a88676fd00affb90cbc9f1ff004ae588103b3"
# proofwidgets
proofwidgets_name := "proofwidgets"
proofwidgets_github := "https://github.com/leanprover-community/ProofWidgets4"
proofwidgets_rev := "eb08eee94098fe530ccd6d8751a86fe405473d4c"
# Cli
cli_name := "cli"
cli_github := "https://github.com/leanprover/lean4-cli"
cli_rev := "2cf1030dc2ae6b3632c84a09350b675ef3e347d0"
# importGraph
import_graph_name := "importGraph"
import_graph_github := "https://github.com/leanprover-community/import-graph"
import_graph_rev := "7376ac07aa2b0492372c056b7a2c3163b3026d1e"
# LeanSearchClient
lean_search_client_name := "LeanSearchClient"
lean_search_client_github := "https://github.com/leanprover-community/LeanSearchClient"
lean_search_client_rev := "4b61d4abc1659f15ffda5ec24fdebc229d51d066"
# mathlib
mathlib_name := "mathlib"
mathlib_github := "https://github.com/leanprover-community/mathlib4"
mathlib_rev := "3ae6376f67d90e32a4dfbee23157ac3ac4b5508c"
# MD4Lean
md4_lean_name := "md4_lean"
md4_lean_github := "https://github.com/acmepjz/md4lean"
md4_lean_rev := "5e95f4776be5e048364f325c7e9d619bb56fb005"
# UnicodeBasic
unicode_basic_name := "unicode_basic"
unicode_basic_github := "https://github.com/fgdorais/lean4-unicode-basic"
unicode_basic_rev := "6d2e06515f1ed1f74208d5a1da3a9cc26c60a7a0"
# BibtexQuery
bibtex_query_name := "bibtex_query"
bibtex_query_github := "https://github.com/dupuisf/BibtexQuery"
bibtex_query_rev := "85e1e7143dd4cfa2b551826c27867bada60858e8"
# «doc-gen4»
doc_gen4_name := "doc_gen4"
doc_gen4_github := "https://github.com/leanprover/doc-gen4"
doc_gen4_rev := "ccb4e97ffb7ad0f9b1852e9669d5e2922f984175"
# project
project_github := "https://github.com/expected-total-cost-of-mdps-in-lean/expected-total-cost-of-mdps-in-lean.github.io"
project_rev := "main"

BAD := env("BAD")
PROJECT := env("PROJECT")

@replace_all:
    just replace {{batteries_name}} {{batteries_github}} {{batteries_rev}}
    just replace {{qq_name}} {{qq_github}} {{qq_rev}}
    just replace {{aesop_name}} {{aesop_github}} {{aesop_rev}}
    just replace {{proofwidgets_name}} {{proofwidgets_github}} {{proofwidgets_rev}}
    just replace {{import_graph_name}} {{import_graph_github}} {{import_graph_rev}}
    just replace {{mathlib_name}} {{mathlib_github}} {{mathlib_rev}}
    just replace {{lean_search_client_name}} {{lean_search_client_github}} {{lean_search_client_rev}}

    LC_CTYPE=C LANG=C find doc/ -type f -exec sed -i '' 's|{{PROJECT}}|{{project_github + "/blob/" + project_rev}}|g' {} +

    # just replace {{cli_name}} {{cli_github}} {{cli_rev}}
    # just replace {{md4_lean_name}} {{md4_lean_github}} {{md4_lean_rev}}
    # just replace {{unicode_basic_name}} {{unicode_basic_github}} {{unicode_basic_rev}}
    # just replace {{bibtex_query_name}} {{bibtex_query_github}} {{bibtex_query_rev}}
    # just replace {{doc_gen4_name}} {{doc_gen4_github}} {{doc_gen4_rev}}

replace name github rev:
    LC_CTYPE=C LANG=C find doc/ -type f -exec sed -i '' 's|{{BAD / name}}|{{github + "/blob/" + rev}}|g' {} +

copy:
    just copy-one doc
    just copy-one pGCL
    just copy-one MDP
    just copy-one lake-manifest.json
    just copy-one lakefile.lean
    just copy-one lean-toolchain
    just copy-one MDP
    just copy-one PGCL
    just copy-one PGCL.lean

    just replace_all

copy-one name:
    rm -rf {{name}}
    cp -r ../pgcl/pGCL/{{name}} ./{{name}}
