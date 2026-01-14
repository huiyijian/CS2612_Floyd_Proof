CURRENT_DIR=.
SETS_DIR = ../sets
FIXPOINT_DIR = ../fixedpoints
MONAD_DIR = ../monadlib
GRAPH_DIR = ../graph_lib
LISTLIB_DIR = ../Listlib
MaxMin_DIR = ../MaxMinLib

COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc$(EXESUF)
COQDEP=$(COQBIN)coqdep$(EXESUF)

COQ_FLAG = -Q $(CURRENT_DIR) Algorithms \
		-R $(SETS_DIR) SetsClass \
		-R $(FIXPOINT_DIR) FP \
		-R $(MONAD_DIR) MonadLib \
		-R $(GRAPH_DIR) GraphLib \
		-R ../coq-record-update/src RecordUpdate \
		-R $(LISTLIB_DIR) ListLib \
		-R $(MaxMin_DIR) MaxMinLib

DEP_FLAG = -Q $(CURRENT_DIR) Algorithms \
		-R $(SETS_DIR) SetsClass \
		-R $(FIXPOINT_DIR) FP \
		-R $(MONAD_DIR) MonadLib \
		-R $(GRAPH_DIR) GraphLib \
		-R ../coq-record-update/src RecordUpdate \
		-R $(LISTLIB_DIR) ListLib \
		-R $(MaxMin_DIR) MaxMinLib

Floyd_FILES = Floyd/Floyd.v 
Dijkstra_FILES = Dijkstra/Dijkstra.v 
Prim_FILES = Prim/Prim.v 
Kruskal_FILES = Kruskal/Kruskal.v


FILES = \
 $(Floyd_FILES) \
 $(Dijkstra_FILES) \
 $(Prim_FILES) \
 $(Kruskal_FILES) \
 MapLib.v

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F)
	@$(COQC) $(COQ_FLAG) $<

all: \
  $(FILES:%.v=%.vo)

_CoqProject:
	@echo $(COQ_FLAG) > _CoqProject

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

-include .depend
