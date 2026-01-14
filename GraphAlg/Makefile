CURRENT_DIR=.

SETS_DIR = sets
LISTLIB_DIR = ListLib
FIXEDPOINTS_DIR = fixedpoints
MAXMINLIB_DIR = MaxMinLib
MONADLIB_DIR = monadlib
GRAPH_LIB_DIR = graph_lib
ALGORITHMS_DIR = algorithms
EXLISTLIB_DIR = ExListLib
RECORDUPDATE_DIR = coq-record-update/src
RECORDUPDATE_ROOT = coq-record-update

COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc$(SUF)
COQDEP=$(COQBIN)coqdep$(SUF)

# Compilation flags for different modules
SETS_FLAG = -R $(SETS_DIR) SetsClass

LISTLIB_FLAG = -Q $(LISTLIB_DIR) ListLib

RECORDUPDATE_FLAG = -Q $(RECORDUPDATE_DIR) RecordUpdate

FIXEDPOINTS_FLAG = -R $(FIXEDPOINTS_DIR) FP \
                   -R $(SETS_DIR) SetsClass

MAXMINLIB_FLAG = -Q $(MAXMINLIB_DIR) MaxMinLib \
                 -R $(SETS_DIR) SetsClass

MONADLIB_FLAG = -R $(MONADLIB_DIR) MonadLib \
                -R $(SETS_DIR) SetsClass \
                -R $(FIXEDPOINTS_DIR) FP

GRAPH_LIB_FLAG = -Q $(GRAPH_LIB_DIR) GraphLib \
                 -R $(SETS_DIR) SetsClass \
                 -R $(ALGORITHMS_DIR) Algorithms \
                 -R $(MAXMINLIB_DIR) MaxMinLib \
                 -R $(LISTLIB_DIR) ListLib

ALGORITHMS_FLAG = -Q $(ALGORITHMS_DIR) Algorithms \
                  -R $(SETS_DIR) SetsClass \
                  -R $(FIXEDPOINTS_DIR) FP \
                  -R $(MONADLIB_DIR) MonadLib \
                  -R $(GRAPH_LIB_DIR) GraphLib \
                  -R $(RECORDUPDATE_DIR) RecordUpdate \
                  -R $(LISTLIB_DIR) ListLib \
                  -R $(MAXMINLIB_DIR) MaxMinLib

EXLISTLIB_FLAG = -R $(EXLISTLIB_DIR) ExListLib \
                 -R $(SETS_DIR) SetsClass \
                 -R $(LISTLIB_DIR) ListLib

# Dependency flags (include all modules)
DEP_FLAG = -R $(SETS_DIR) SetsClass \
           -Q $(LISTLIB_DIR) ListLib \
           -Q $(RECORDUPDATE_DIR) RecordUpdate \
           -R $(FIXEDPOINTS_DIR) FP \
           -Q $(MAXMINLIB_DIR) MaxMinLib \
           -R $(MONADLIB_DIR) MonadLib \
           -Q $(GRAPH_LIB_DIR) GraphLib \
           -Q $(ALGORITHMS_DIR) Algorithms \
           -R $(EXLISTLIB_DIR) ExListLib

# Sets files
SETS_FILE_NAMES = \
    SetsClass.v \
    SetsClass_AxiomFree.v \
    SetsDomain.v \
    SetElement.v \
    SetElementProperties.v \
    RelsDomain.v \
    SetProd.v \
    SetsDomain_Classic.v

SETS_TEST_FILES = Test.v

SETS_FILES=$(SETS_FILE_NAMES:%.v=$(SETS_DIR)/%.v)
SETS_TEST=$(SETS_TEST_FILES:%.v=$(SETS_DIR)/%.v)

# ListLib files
LISTLIB_BASE_FILES = \
    Inductive.v \
    Positional.v

LISTLIB_GENERAL_FILES = \
    Forall.v \
    IndexedElements.v \
    Length.v \
    Presuffix.v

LISTLIB_FILES=$(LISTLIB_BASE_FILES:%.v=$(LISTLIB_DIR)/Base/%.v) \
              $(LISTLIB_GENERAL_FILES:%.v=$(LISTLIB_DIR)/General/%.v)

# RecordUpdate files
RECORDUPDATE_FILE_NAMES = \
    Lens.v \
    RecordEta.v \
    RecordSet.v \
    RecordUpdate.v

RECORDUPDATE_FILES=$(RECORDUPDATE_FILE_NAMES:%.v=$(RECORDUPDATE_DIR)/%.v)

# Fixedpoints files
FIXEDPOINTS_FILE_NAMES = \
    AllFramework.v \
    Coqlib.v \
    LiftConstructors.v \
    PartialOrder_Setoid.v \
    KnasterTarski.v \
    BourbakiWitt.v \
    SetsFixedpoints.v

FIXEDPOINTS_FILES=$(FIXEDPOINTS_FILE_NAMES:%.v=$(FIXEDPOINTS_DIR)/%.v)

# MaxMinLib files
MAXMINLIB_FILE_NAMES = \
    Interface.v \
    MaxMin.v

MAXMINLIB_FILES=$(MAXMINLIB_FILE_NAMES:%.v=$(MAXMINLIB_DIR)/%.v)

# MonadLib files
MONADLIB_BASE_FILES = \
    Monad.v \
    MonadLib.v

MONADLIB_SETMONAD_FILES = \
    SetBasic.v \
    SetHoare.v \
    FixpointLib.v \
    SetMonad.v

MONADLIB_STATERELMONAD_FILES = \
    StateRelBasic.v \
    StateRelHoare.v \
    FixpointLib.v \
    safeexec_lib.v \
    StateRelMonad.v

MONADLIB_MONADERR_FILES = \
    MonadErrBasic.v \
    MonadErrLoop.v \
    MonadErrHoare.v \
    monadesafe_lib.v \
    StateRelMonadErr.v

MONADLIB_OPTIONMONAD_FILES = \
    OptionBasic.v \
    OptionMonad.v

MONADLIB_LISTMONAD_FILES = \
    ListBasic.v \
    ListMonad.v

MONADLIB_FILES=$(MONADLIB_BASE_FILES:%.v=$(MONADLIB_DIR)/%.v) \
               $(MONADLIB_SETMONAD_FILES:%.v=$(MONADLIB_DIR)/SetMonad/%.v) \
               $(MONADLIB_STATERELMONAD_FILES:%.v=$(MONADLIB_DIR)/StateRelMonad/%.v) \
               $(MONADLIB_MONADERR_FILES:%.v=$(MONADLIB_DIR)/MonadErr/%.v) \
               $(MONADLIB_OPTIONMONAD_FILES:%.v=$(MONADLIB_DIR)/OptionMonad/%.v) \
               $(MONADLIB_LISTMONAD_FILES:%.v=$(MONADLIB_DIR)/ListMonad/%.v)

# Graph library files
GRAPH_LIB_FILE_NAMES = \
    graph_basic.v \
    Syntax.v \
    GraphLib.v \
    reachable/reachable_basic.v \
    reachable/reachable_restricted.v \
    reachable/path_basic.v \
    reachable/path.v \
    reachable/vpath.v \
    reachable/epath.v \
    reachable/eweight.v \
    reachable/Zweight.v \
    directed/rootedtree.v \
    subgraph/subgraph.v \
    undirected/undirected_basic.v \
    undirected/tree.v \
    examples/floyd.v \
    examples/dijkstra.v \
    examples/prim.v \
    examples/kruskal.v

GRAPH_LIB_FILES=$(GRAPH_LIB_FILE_NAMES:%.v=$(GRAPH_LIB_DIR)/%.v)

# Algorithms files
ALGORITHMS_FILE_NAMES = \
    MapLib.v \
    Floyd/Floyd.v \
    Dijkstra/Dijkstra.v \
    Prim/Prim.v \
    Kruskal/Kruskal.v

ALGORITHMS_FILES=$(ALGORITHMS_FILE_NAMES:%.v=$(ALGORITHMS_DIR)/%.v)

# ExListLib files (optional - if needed)
EXLISTLIB_FILE_NAMES = \
    ZList.v \
    InvertalList.v \
    Nperm.v \
    Presuffix.v \
    Sorting.v

EXLISTLIB_FILES=$(EXLISTLIB_FILE_NAMES:%.v=$(EXLISTLIB_DIR)/%.v)

# All files
FILES = $(SETS_FILES) \
        $(SETS_TEST) \
        $(LISTLIB_FILES) \
        $(RECORDUPDATE_FILES) \
        $(FIXEDPOINTS_FILES) \
        $(MAXMINLIB_FILES) \
        $(MONADLIB_FILES) \
        $(GRAPH_LIB_FILES) \
        $(ALGORITHMS_FILES)

# Compilation rules for each module
$(SETS_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F)
	@$(COQC) $(SETS_FLAG) $<

$(SETS_TEST:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F)
	@$(COQC) $(SETS_FLAG) $<

$(LISTLIB_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F)
	@$(COQC) $(LISTLIB_FLAG) $<

$(RECORDUPDATE_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F)
	@$(COQC) $(RECORDUPDATE_FLAG) $<

$(FIXEDPOINTS_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F)
	@$(COQC) $(FIXEDPOINTS_FLAG) $<

$(MAXMINLIB_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F)
	@$(COQC) $(MAXMINLIB_FLAG) $<

$(MONADLIB_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F)
	@$(COQC) $(MONADLIB_FLAG) $<

$(GRAPH_LIB_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F)
	@$(COQC) $(GRAPH_LIB_FLAG) $<

$(ALGORITHMS_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F)
	@$(COQC) $(ALGORITHMS_FLAG) $<

$(EXLISTLIB_FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $(<F)
	@$(COQC) $(EXLISTLIB_FLAG) $<

# Main target
all: $(FILES:%.v=%.vo)

# Help target
help:
	@echo "Available targets:"
	@echo "  all      - Build all Coq files (default)"
	@echo "  clean    - Remove all compiled files"
	@echo "  depend   - Generate dependency file"
	@echo "  _CoqProject - Generate _CoqProject file"
	@echo ""
	@echo "Modules:"
	@echo "  - SetsClass (sets/)"
	@echo "  - ListLib (ListLib/)"
	@echo "  - RecordUpdate (coq-record-update/src/)"
	@echo "  - Fixedpoints (fixedpoints/)"
	@echo "  - MaxMinLib (MaxMinLib/)"
	@echo "  - MonadLib (monadlib/)"
	@echo "  - GraphLib (graph_lib/)"
	@echo "  - Algorithms (algorithms/)"
	@echo "  - ExListLib (ExListLib/)"

# Generate _CoqProject file
_CoqProject:
	@echo $(DEP_FLAG) > _CoqProject

# Generate dependencies
depend: $(FILES)
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend: $(FILES)
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

# Clean compiled files
clean:
	@rm -f *.glob */*.glob */*/*.glob */*/*/*.glob
	@rm -f *.vo */*.vo */*/*.vo */*/*/*.vo
	@rm -f *.vok */*.vok */*/*.vok */*/*/*.vok
	@rm -f *.vos */*.vos */*/*.vos */*/*/*.vos
	@rm -f .*.aux */.*.aux */*/.*.aux */*/*/.*.aux
	@rm -f .depend
	@rm -f $(MONADLIB_DIR)/*/*.vo $(MONADLIB_DIR)/*/*.glob $(MONADLIB_DIR)/*/*.vos $(MONADLIB_DIR)/*/*.vok $(MONADLIB_DIR)/*/.*.aux
	@rm -f $(RECORDUPDATE_DIR)/*.vo $(RECORDUPDATE_DIR)/*.glob $(RECORDUPDATE_DIR)/*.vos $(RECORDUPDATE_DIR)/*.vok $(RECORDUPDATE_DIR)/.*.aux
	@rm -f $(LISTLIB_DIR)/*/*.vo $(LISTLIB_DIR)/*/*.glob $(LISTLIB_DIR)/*/*.vos $(LISTLIB_DIR)/*/*.vok $(LISTLIB_DIR)/*/.*.aux
	@rm -f $(GRAPH_LIB_DIR)/*/*.vo $(GRAPH_LIB_DIR)/*/*.glob $(GRAPH_LIB_DIR)/*/*.vos $(GRAPH_LIB_DIR)/*/*.vok $(GRAPH_LIB_DIR)/*/.*.aux
	@rm -f $(GRAPH_LIB_DIR)/*/*/*.vo $(GRAPH_LIB_DIR)/*/*/*.glob $(GRAPH_LIB_DIR)/*/*/*.vos $(GRAPH_LIB_DIR)/*/*/*.vok $(GRAPH_LIB_DIR)/*/*/.*.aux
	@rm -f $(ALGORITHMS_DIR)/*/*.vo $(ALGORITHMS_DIR)/*/*.glob $(ALGORITHMS_DIR)/*/*.vos $(ALGORITHMS_DIR)/*/*.vok $(ALGORITHMS_DIR)/*/.*.aux
	@echo "Cleaned all compiled files"

.PHONY: all clean depend _CoqProject help
.DEFAULT_GOAL := all

-include .depend

