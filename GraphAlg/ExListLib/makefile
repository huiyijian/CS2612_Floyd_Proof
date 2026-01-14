CURRENT_DIR=.

-include CONFIGURE

COQC=$(COQBIN)coqc$(EXESUF)
COQDEP=$(COQBIN)coqdep$(EXESUF)

COQ_FLAG = -Q $(CURRENT_DIR) ExListLib \
		   -R ../sets SetsClass \
		   -R ../ListLib ListLib
DEP_FLAG = -Q $(CURRENT_DIR) ExListLib \
		   -R ../sets SetsClass \
		   -R ../ListLib ListLib

EX_LIST_FILES = ZList.v \
	InvertalList.v Nperm.v Presuffix.v Sorting.v

FILES = \
 $(EX_LIST_FILES) \

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v

world: \
  $(FILES:%.v=%.vo)

all: world 

depend:
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend:
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm -f *.glob */*.glob;
	@rm -f *.vo */*.vo;
	@rm -f *.vok */*.vok;
	@rm -f *.vos */*.vos;
	@rm -f .*.aux */.*.aux;
	@rm -f .depend;

.DEFAULT_GOAL := all

include .depend

