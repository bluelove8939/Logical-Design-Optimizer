import typing
import math
import logging
import itertools

from tools import TruthTable, BinValue, Implicant
from custom_exceptions import *


class SequenceGenerator:
    def __init__(self, sequence:typing.Iterable[int]=None):
        self._sequence = None
        self._stateset = None
        self._statenum = None
        self._isInitialized = False

        if sequence is not None:
            self.setSequence(sequence)

    def setSequence(self, sequence:typing.Iterable[int]):
        if len(sequence) == 0:
            raise InvalidSequenceException(f"length of sequence cannot be 0")

        self._sequence = sequence
        self._statenum = 0
        self._stateset = set()

        for item in self._sequence:
            if item not in self._stateset:
                self._stateset.add(item)
                self._statenum += 1

        self._isInitialized = True

    def generateDesign(self, max_iter=10000, verbose=False, verbose_level=logging.DEBUG):
        if verbose:
            logging.basicConfig(level=verbose_level)

        in_bitsiz  = math.ceil(math.log2(len(self._sequence)))    # input bit size
        out_bitsiz = in_bitsiz                                    # output bit size
        state_bitsiz = math.ceil(math.log2(len(self._stateset)))  # state bit size

        # Encode state as binary number
        encoded_state = {}  # states encoded as binary value
        for state_key in self._stateset:
            if isinstance(state_key, int):
                encoded_state[state_key] = BinValue(value=state_key, dcare=0, bitsiz=state_bitsiz)
            else:
                raise InvalidTypeException('sequence element', 'int', type(state_key).__name__)
        encoded_state_keylist = encoded_state.keys()  # keylist of encoded states (used for iteration of encoded states)

        # Generate all of the available sequences
        sequence_encoded_state = {}  # states encoded with sequence elements
        for state_key in encoded_state_keylist:
            sequence_encoded_state[state_key] = []
            state_binvalue = BinValue(value=state_key, dcare=0, bitsiz=state_bitsiz)

            for val in range(2 ** in_bitsiz):
                in_binvalue = BinValue(value=val, dcare=0, bitsiz=in_bitsiz)
                if in_binvalue.endswith(state_binvalue) and in_binvalue not in sequence_encoded_state[state_key]:
                    sequence_encoded_state[state_key].append(in_binvalue)

        # Generate permuation of sequence encoded result
        sequence_permutation_state = {}  # permitation of state sequence elements
        for state_key in encoded_state_keylist:
            sequence_permutation_state[state_key] = []
            for perm in itertools.permutations(sequence_encoded_state[state_key]):
                sequence_permutation_state[state_key].append(perm)

        if verbose:
            logging.debug(f"stateset: {self._stateset}")
            logging.debug(f"sequence: {self._sequence}")
            logging.debug(f"state_keylist: {encoded_state_keylist}")
            logging.debug(f"in_bitsize: {in_bitsiz}")
            logging.debug(f"out_bitsize: {out_bitsiz}")
            logging.debug(f"state_bitsize: {state_bitsiz}")

            for key, value in sequence_encoded_state.items():
                logging.debug(f"sequence_encoded_state[{key}]: {' '.join(list(map(str, value)))}")

        # Generate truth tables and corresponding expressions
        results = None  # extracted expressions
        min_score = in_bitsiz * in_bitsiz * in_bitsiz * 2 * 100
        selected_idx = [0] * len(encoded_state_keylist)  # selected index of permutation
        maximum_idx = [len(sequence_permutation_state[state_key])-1 for state_key in encoded_state_keylist]

        iter_max = 1
        iter_cnt = 0
        for num in maximum_idx:
            iter_max *= num
        iter_max = min(max_iter, iter_max)

        if verbose:
            logging.debug(f"maximum index: {maximum_idx}")

        while True:
            # [1] Extract selected permutation
            selected_permutation = {}  # stores selected permuation (key, value) = (state_key, permutation)
            cursors = {}
            for state_idx, state_key in enumerate(encoded_state_keylist):
                selected_permutation[state_key] = sequence_permutation_state[state_key][selected_idx[state_idx]]
                cursors[state_key] = 0

            # [2] Sequence generation
            named_sequence = []  # binary encoded sequence
            for seq_element in self._sequence:  # seq_element needs to be included by encoded_state_keylist
                cursor_val = cursors[seq_element]
                named_element = selected_permutation[seq_element][cursor_val]  # binary value of corresponding seq_element
                named_sequence.append(named_element)
                cursors[seq_element] += 1

            if verbose:
                print(f"\riteration:{iter_cnt}/{iter_max}({iter_cnt/iter_max*100:.2f}%)", end="")
                logging.debug(f"selected_idx: {selected_idx}  named_sequence: {', '.join(list(map(str, named_sequence)))}")

            # [3] Truth table generation (state transition)
            #   input:  binary encoded state_key
            #   output: named sequence element
            #
            #   Example)
            #     named_seqence: 2'b01, 2'b11, 2'b00, 2'b10
            #     input | Output
            #     --------------
            #        00 |    10
            #        01 |    11
            #        10 |    01
            #        11 |    00
            state_transition_table = TruthTable(in_siz=in_bitsiz, out_siz=in_bitsiz)  # bitsiz of named_element is in_bitsiz
            for named_idx, named_element in enumerate(named_sequence):
                nxt_named_element = named_sequence[named_idx+1] if named_idx < len(named_sequence)-1 else named_sequence[0]
                state_transition_table.setValue(idx=named_element, val=nxt_named_element)

            jk_excitation = TruthTable(in_siz=2, out_siz=2)
            jk_excitation.setValue(idx=BinValue(value=0, dcare=0, bitsiz=2), val=BinValue(value=0, dcare=1, bitsiz=2))
            jk_excitation.setValue(idx=BinValue(value=1, dcare=0, bitsiz=2), val=BinValue(value=2, dcare=1, bitsiz=2))
            jk_excitation.setValue(idx=BinValue(value=2, dcare=0, bitsiz=2), val=BinValue(value=1, dcare=2, bitsiz=2))
            jk_excitation.setValue(idx=BinValue(value=3, dcare=0, bitsiz=2), val=BinValue(value=0, dcare=2, bitsiz=2))

            converted_table = state_transition_table.stateTransitionConversion(excitation_table=jk_excitation)
            exprs = converted_table.searchMinimumExpr()

            score = 0
            for expr in exprs:
                score += 1
                for impl in expr:
                    score += impl.countLiterals()

            if score <= min_score:
                results = SequenceLogicDesign(in_siz=in_bitsiz, seq_siz=state_bitsiz, exprs=exprs,
                                              state_transition_table=state_transition_table,
                                              converted_table=converted_table)

            # if verbose:
            #     for lidx, line in enumerate(exprs):
            #         logging.info(f"expr{lidx}: {' '.join(list(map(str, line)))}")
            #     logging.info("==================")

            if selected_idx == maximum_idx:
                break

            if iter_cnt >= iter_max:
                break
            iter_cnt += 1

            selected_idx[0] += 1
            for pivot in range(len(selected_idx)):
                if selected_idx[pivot] > maximum_idx[pivot]:
                    if pivot < len(selected_idx) - 1:
                        selected_idx[pivot] = 0
                        selected_idx[pivot + 1] += 1
                else:
                    break

        return results


class LogicDesign(object):
    def __init__(self, in_siz:int, out_siz:int, exprs:typing.Iterable, **metadata):
        self._in_siz = in_siz
        self._out_siz = out_siz
        self.exprs = exprs
        self.metadata = metadata

        for expr in exprs:
            if not isinstance(expr, typing.Iterable):
                raise InvalidTypeException('expression', right="iterables", wrong=type(expr).__name__)
            for impl in expr:
                if not isinstance(impl, Implicant):
                    raise InvalidTypeException('term inside expression', right="Implicant", wrong=type(impl).__name__)

    def countScore(self):
        score = 0
        for expr in self.exprs:
            score += 1
            for impl in expr:
                score += impl.countLiterals()


class SequenceLogicDesign(LogicDesign):
    def __init__(self, in_siz:int, seq_siz:int, exprs:typing.Iterable, **metadata):
        super(SequenceLogicDesign, self).__init__(in_siz=in_siz, out_siz=in_siz, exprs=exprs, **metadata)
        self.seq_siz = seq_siz


if __name__ == '__main__':
    manager = SequenceGenerator()
    manager.setSequence([0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0])
    results = manager.generateDesign(max_iter=10000, verbose=True, verbose_level=logging.INFO)
    for eidx, expr in enumerate(results.exprs):
        print(f"expr{eidx}: {' '.join(list(map(str, expr)))}")
    print(f"State transition truth table: {' '.join(list(map(str, results.metadata['state_transition_table'].values)))}")
    print(f"Converted table: {' '.join(list(map(str, results.metadata['converted_table'].values)))}")