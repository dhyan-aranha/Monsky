
.PHONY: default

default:
	lake build

LEAN_FILES := $(wildcard Monsky/*.lean)

dependencies.svg: dependencies.dot
	dot -Tsvg dependencies.dot > $@

dependencies.dot: $(LEAN_FILES)
	@echo "digraph {" > $@
	@$(foreach file, $^ ,\
		if grep -q "sorry" "$(file)"; then \
			echo "$(basename $(notdir $(file))) [ label = \"$(basename $(notdir $(file)))?\", color="red", href = \"$(BASE)$(basename $(notdir $(file))).html\" ]" >> $@; \
		else \
			echo "$(basename $(notdir $(file))) [ label = \"$(basename $(notdir $(file)))✓\", color="green", href = \"$(BASE)$(basename $(notdir $(file))).html\" ]" >> $@; \
		fi;)
	@(grep -nr "import Monsky" Monsky/*.lean | awk -F '[./]' '{print $$4 " -> " $$2}') >> $@
	@echo "}" >> $@
