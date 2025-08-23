##
# Doc Generation Makefile
#
# @file
# @version 0.1

all:
	DOCGEN_SRC="github" lake build FraudProof:docs

update:
	MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4

serve:
	cd .lake/build/doc; python3 -m http.server

publish:
	cp -r .lake/build/doc/* ../docs/

# end
