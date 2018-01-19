LEC_TEMPLATE := tex/lecture.tex

CWD := $(shell pwd)
SEP := :

# Use our directory of TeX resources in all builds.
# For TEXINPUTS, the trailing $(SEP) says to use the standard search paths too.
# For BIBINPUTS, we need to use an absolute path because bibtex will be run in
# the bib directory.
TEXDIR := tex
export TEXINPUTS = $(TEXDIR)$(SEP)
export BIBINPUTS = $(CWD)/$(TEXDIR)

.PHONY: all
all: lectures
clean:
	rm -rf build

# Build a single lecture.
build/lectures/%.pdf: lectures/%/content.tex
	@mkdir -p build/lectures
	latexmk -xelatex -output-directory=build/lectures -jobname=$* $(LEC_TEMPLATE)

# All the lectures.
.PHONY: lectures
LECTURE_TEX := $(wildcard lectures/*/content.tex)
LECTURE_PDF := $(LECTURE_TEX:lectures/%/content.tex=build/lectures/%.pdf)
lectures: $(LECTURE_PDF)
