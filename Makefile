.DEFAULT_GOAL := all

PROJECT = AbstractAlgebraInLean

.PHONY: all build blueprint blueprint-dev analyze serve

all : build blueprint

build:
	(lake exe cache get && lake build)

blueprint: build
	(cd blueprint && inv all)

analyze:
	(python3 blueprint/blueprint_auto.py -p ${PROJECT})

serve: blueprint
	(cd blueprint && inv serve)