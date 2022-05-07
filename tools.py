import typing

from custom_exceptions import *


class TruthTable(object):
    def __init__(self, in_siz:int, out_siz:int, values:(None, typing.List)=None):
        self._in_siz = in_siz
        self._out_siz = out_siz
        self.values = values

        if self.values is None:
            self.values = [BinValue(value=0, bitsiz=self._out_siz)] * (2 ** self._in_siz)
        else:
            for idx, item in enumerate(self.values):
                if isinstance(item, int):
                    self.values[idx] = BinValue(value=item, dcare=2**self._out_siz-1, bitsiz=self._out_siz)
                elif not isinstance(item, BinValue):
                    raise Exception(f'Error ocurred on generating truth table: invalid value {item}')
                else:
                    self.values[idx] = BinValue(value=item.value, dcare=item.dcare, bitsiz=self._out_siz)

    def getSize(self):
        return self._in_siz, self._out_siz

    def setValue(self, idx, val):
        if not isinstance(idx, BinValue):
            raise InvalidTypeException('idx', 'BinValue', type(idx).__name__)
        if not isinstance(val, BinValue):
            raise InvalidTypeException('val', 'BinValue', type(val).__name__)
        if idx.dcare != 0:
            raise InvalidBinValueException('idx cannot have any dont care literal')
        if idx.value > 2 ** self._in_siz - 1:
            raise InvalidIndexException(idx)
        if val.value > 2 ** self._out_siz - 1:
            raise InvalidValueException(val)
        self.values[idx.value] = BinValue(value=val.value, dcare=val.dcare, bitsiz=self._out_siz)

    def getValue(self, idx):
        if not isinstance(idx, BinValue):
            raise InvalidTypeException('idx', 'BinValue', type(idx).__name__)
        if idx.dcare != 0:
            raise InvalidBinValueException('idx cannot have any dont care literal')
        return self.values[idx.value]

    def searchMinimumTargetExprs(self, target, only_min=True):
        if not isinstance(target, BinValue):
            raise InvalidTypeException('target_idx', 'BinValue', type(target).__name__)

        # 1. Make a list of every implicants needs to be covered
        implicants_ids = []  # index of single implicants needs to be covered
        implicants = []      # single implicants
        for in_idx, item in enumerate(self.values):
            if item.dcare & target.value != 0:
                implicants.append(Implicant(binvalue=BinValue(value=in_idx, bitsiz=self._in_siz)))
            elif item.value & target.value != 0:
                implicants_ids.append(in_idx)
                implicants.append(Implicant(binvalue=BinValue(value=in_idx, bitsiz=self._in_siz)))

        # 2. Determine prime implicants
        prime_implicants = []  # prime implicants
        combined = []

        while len(implicants):
            flags = [False] * len(implicants)
            for i in range(len(implicants)):
                for j in range(i + 1, len(implicants)):
                    a = implicants[i]
                    b = implicants[j]
                    flag, combined_result = a.combine(b)
                    if flag:
                        # print(f"combine {a} and {b}: result: {combined_result}")
                        flags[i] = True
                        flags[j] = True
                        if combined_result not in combined:
                            combined.append(combined_result)

            for idx, val in enumerate(flags):
                if not val:
                    prime_implicants.append(implicants[idx])

            implicants = combined[:]
            combined = []

        # 3. Find every combination of prime implicants to cover all of the implicants (Petrick's method)
        implicants_map = {}  # implicants map (key, value) = (index of implicant, list of prime implicants covering this implicant)
        for impl_id in implicants_ids:
            implicants_map[impl_id] = []

        for pidx, pimp in enumerate(prime_implicants):
            for impl_id in implicants_ids:
                if impl_id in pimp.including_ids:
                    implicants_map[impl_id].append(pidx)

        results = []
        selected_idx = [0] * len(implicants_ids)
        maximum_idx = [len(implicants_map[impl_id])-1 for impl_id in implicants_ids]

        while True:
            expr = set()
            for pos, sel_idx in enumerate(selected_idx):
                impl_id = implicants_ids[pos]
                pimp_id = implicants_map[impl_id][sel_idx]
                if pimp_id not in expr:
                    expr.add(pimp_id)

            if expr not in results:
                results.append(expr)

            if selected_idx == maximum_idx:
                break

            selected_idx[0] += 1
            for pivot in range(len(selected_idx)):
                if selected_idx[pivot] > maximum_idx[pivot]:
                    if pivot < len(selected_idx)-1:
                        selected_idx[pivot] = 0
                        selected_idx[pivot+1] += 1
                else:
                    break

        final_exprs = []

        for row in results:
            final_exprs.append([])
            for item in row:
                final_exprs[-1].append(prime_implicants[item])

        if only_min:
            min_cnt = (2 ** self._in_siz) * self._in_siz + 1
            min_final_exprs = []
            for row in final_exprs:
                cnt = 0
                for item in row:
                    cnt += item.countLiterals()
                if cnt < min_cnt:
                    min_final_exprs = [row]
                    min_cnt = cnt
                elif cnt == min_cnt:
                    min_final_exprs.append(row)
            final_exprs = min_final_exprs

        return final_exprs

    def searchMinimumExpr(self):
        results = []
        for target_idx in range(self._out_siz):
            target = BinValue(value=1 << target_idx, dcare=0, bitsiz=self._out_siz)
            min_exprs = self.searchMinimumTargetExprs(target=target, only_min=True)
            results.append(min_exprs[0])
        return results

    def stateTransitionConversion(self, excitation_table):
        if not isinstance(excitation_table, TruthTable):
            raise InvalidTypeException('excitation_table', 'TruthTable', type(excitation_table).__name__)
        if self._in_siz != self._out_siz:
            raise BitsizDismatchException('to convert bitwise, bit size needs to be matched')

        exc_in_siz, exc_out_siz = excitation_table.getSize()
        result_table = TruthTable(in_siz=self._in_siz, out_siz=self._out_siz*exc_out_siz)

        for idx in range(2 ** self._in_siz):
            bin_idx = BinValue(value=idx, dcare=0, bitsiz=self._in_siz)
            bin_val = self.values[idx]
            out_val = 0
            out_dca = 0
            out_bsiz = 0

            for bit_pos in range(self._in_siz):
                mask = 1 << bit_pos
                bin_idx_mask = bin_idx.value & mask
                bin_val_mask = bin_val.value & mask

                if bin_val.dcare:
                    out_dca += (2**exc_out_siz-1) * (1 << out_bsiz)
                else:
                    exc_in_bin_val = 0
                    exc_in_bin_val += 1 if bin_val_mask == mask else 0
                    exc_in_bin_val += 2 if bin_idx_mask == mask else 0
                    out_val += excitation_table.values[exc_in_bin_val].value * (1 << out_bsiz)
                    out_dca += excitation_table.values[exc_in_bin_val].dcare * (1 << out_bsiz)

                out_bsiz += exc_out_siz

            result_table.setValue(idx=bin_idx, val=BinValue(value=out_val, dcare=out_dca, bitsiz=out_bsiz))

        return result_table


class Implicant(object):
    def __init__(self, binvalue, eliminated=0):
        self.binvalue = binvalue
        self.including_ids = [self.binvalue.value]
        self.eliminated = eliminated

        if self.binvalue.dcare != 0:
            raise InvalidBinValueException("binary value containing any dont care implicant cannot be implicant")

    def countLiterals(self):
        cnt = 0
        for idx in range(self.binvalue.bitsiz):
            if self.eliminated & 1 << idx != 0:
                cnt += 1
        return self.binvalue.bitsiz - cnt

    def combine(self, other):
        if not isinstance(other, Implicant):
            raise InvalidTypeException(varname='other', right='Implicant', wrong=type(other).__name__)
        if self.binvalue.bitsiz != other.binvalue.bitsiz:
            raise InvalidImplicantException(msg="bitsize needs to be matched to combine two implicants")

        eliminate_idx = 0
        cnt = 0

        for idx in range(self.binvalue.bitsiz):
            s_val = self.binvalue.value & 1 << idx
            o_val = other.binvalue.value & 1 << idx
            s_ebit = self.eliminated & 1 << idx
            o_ebit = other.eliminated & 1 << idx

            if s_val != o_val:
                if s_ebit == 0 and o_ebit == 0:
                    eliminate_idx = idx
                    cnt += 1

        flag = cnt == 1 and self.eliminated == other.eliminated
        result = Implicant(binvalue=self.binvalue.logicalAnd(other.binvalue), eliminated=self.eliminated)

        if flag:
            result.eliminated += 1 << eliminate_idx
            result.including_ids = self.including_ids + other.including_ids

        return flag, result

    def __str__(self) -> str:
        if self.binvalue.bitsiz > 26:
            raise Exception(f'Error ocurred on generating implicant: Bit size is too large ({self.binvalue.bitsiz})')
        result = ""
        mask = 1
        for idx in reversed(range(self.binvalue.bitsiz)):
            if self.eliminated & (mask << idx) != 0:
                result += '-'
            elif self.binvalue.value & (mask << idx) == 0:
                result += '0'
            else:
                result += '1'
        return result

    def __eq__(self, other):
        return str(self) == str(other)


class BinValue(object):
    def __init__(self, value: int, dcare: int=0, bitsiz:(int, None)=None):
        self.value = value
        self.dcare = dcare
        self.bitsiz = 32 if bitsiz is None else bitsiz
        if self.value > 2 ** self.bitsiz-1:
            raise InvalidValueException(val=value)

    def __add__(self, other):
        if isinstance(other, int):
            return BinValue(self.value + other, dcare=self.dcare, bitsiz=self.bitsiz)
        elif isinstance(other, BinValue):
            return BinValue(self.value + other.value, dcare=self.dcare, bitsiz=self.bitsiz)
        else:
            raise InvalidTypeException(varname="other", right="int or BinValue", wrong=f"{type(other).__name__}")

    def __sub__(self, other):
        if isinstance(other, int):
            return BinValue(self.value - other, dcare=self.dcare, bitsiz=self.bitsiz)
        elif isinstance(other, BinValue):
            return BinValue(self.value - other.value, dcare=self.dcare, bitsiz=self.bitsiz)
        else:
            raise InvalidTypeException(varname="other", right="int or BinValue", wrong=f"{type(other).__name__}")

    def __radd__(self, other):
        return self.__add__(other)

    def __rsub__(self, other):
        return BinValue(value=-1*self.value).__add__(other)

    def __iadd__(self, other):
        if isinstance(other, int):
            self.value += other
        elif isinstance(other, BinValue):
            self.value += other.value
        else:
            raise InvalidTypeException(varname="other", right="int or BinValue", wrong=f"{type(other).__name__}")
        return self

    def __isub__(self, other):
        if isinstance(other, int):
            self.value -= other
        elif isinstance(other, BinValue):
            self.value -= other.value
        else:
            raise InvalidTypeException(varname="other", right="int or BinValue", wrong=f"{type(other).__name__}")
        return self

    def __eq__(self, other):
        if isinstance(other, int):
            return self.value == other
        elif isinstance(other, BinValue):
            return self.value == other.value and self.dcare == other.dcare
        else:
            raise InvalidTypeException(varname="other", right="int or BinValue", wrong=f"{type(other).__name__}")

    def endswith(self, other):
        if not isinstance(other, BinValue):
            raise InvalidTypeException(varname='other', right='BinValue', wrong=type(other).__name__)
        flag = True
        for idx in range(other.bitsiz):
            if (other.value & 1 << idx) != (self.value & 1 << idx):
                flag = False
                break
        return flag

    @classmethod
    def concat(cls, *args):
        val = 0
        dca = 0
        bsiz = 0
        for arg in args:
            if not isinstance(arg, BinValue):
                raise InvalidTypeException(varname='concat arguments', right='BinValue', wrong=type(arg).__name__)
            val += arg.value * (1 << bsiz)
            dca += arg.dcare * (1 << bsiz)
            bsiz += arg.bitsiz
        return BinValue(value=val, dcare=dca, bitsiz=bsiz)

    def maxval(self) -> int:
        return 2 ** self.bitsiz - 1

    def setbit(self, *args):
        for arg in args:
            if (isinstance(arg, int) or (isinstance(arg, float) and arg % 1 == 0)) and arg < self.bitsiz:
                self.value |= 1 << arg
            else:
                raise InvalidIndexException(f'InvalidIndexException ocurred: invalid index {arg}')

    def clearbit(self, *args):
        for arg in args:
            if (isinstance(arg, int) or (isinstance(arg, float) and arg % 1 == 0)) and arg < self.bitsiz:
                self.value &= ~(1 << arg)
            else:
                raise InvalidIndexException(f'InvalidIndexException ocurred: invalid index {arg}')

    def togglebit(self, *args):
        for arg in args:
            if (isinstance(arg, int) or (isinstance(arg, float) and arg % 1 == 0)) and arg < self.bitsiz:
                self.value ^= 1 << arg
            else:
                raise InvalidIndexException(f'InvalidIndexException ocurred: invalid index {arg}')

    def setDontCarebit(self, *args):
        for arg in args:
            if (isinstance(arg, int) or (isinstance(arg, float) and arg % 1 == 0)) and arg < self.bitsiz:
                self.dcare |= 1 << arg
            else:
                raise InvalidIndexException(f'InvalidIndexException ocurred: invalid index {arg}')

    def clearDontCarebit(self, *args):
        for arg in args:
            if (isinstance(arg, int) or (isinstance(arg, float) and arg % 1 == 0)) and arg < self.bitsiz:
                self.dcare &= ~(1 << arg)
            else:
                raise InvalidIndexException(f'InvalidIndexException ocurred: invalid index {arg}')

    def toggleDontCarebit(self, *args):
        for arg in args:
            if (isinstance(arg, int) or (isinstance(arg, float) and arg % 1 == 0)) and arg < self.bitsiz:
                self.dcare ^= 1 << arg
            else:
                raise InvalidIndexException(f'InvalidIndexException ocurred: invalid index {arg}')

    def logicalOr(self, other, ignore_dcare=True, inclusive_dcare=False):
        if not isinstance(other, BinValue):
            raise InvalidTypeException(varname="other", right="BinValue", wrong=type(other).__name__)
        if self.bitsiz != other.bitsiz:
            raise BitsizDismatchException()

        result_value = 0
        result_dcare = 0

        if not ignore_dcare:
            mask = 1
            for idx in range(self.bitsiz):
                bit_act = mask << idx
                s_val = self.value & bit_act   # self value bit
                s_dca = self.dcare & bit_act   # self dcare bit
                o_val = other.value & bit_act  # other value bit
                o_dca = other.dcare & bit_act  # other dcare bit

                r_val = 0  # result value bit
                r_dca = 0  # result dcare bit

                if s_dca == bit_act and o_dca == bit_act:
                    r_dca = bit_act
                elif s_dca == bit_act:
                    if o_val == bit_act:
                        r_val = bit_act
                    else:
                        if not inclusive_dcare:
                            raise DcareDismatchException()
                        r_dca = bit_act
                elif o_dca == bit_act:
                    if s_val == bit_act:
                        r_val = mask << idx
                    else:
                        if not inclusive_dcare:
                            raise DcareDismatchException()
                        r_dca = bit_act
                else:
                    r_val = s_val | o_val

                result_value += r_val
                result_dcare += r_dca
        else:
            result_value = self.value | other.value

        return BinValue(value=result_value, dcare=result_dcare, bitsiz=self.bitsiz)

    def logicalAnd(self, other, ignore_dcare=True, inclusive_dcare=False):
        if not isinstance(other, BinValue):
            raise InvalidTypeException(varname="other", right="BinValue", wrong=type(other).__name__)
        if self.bitsiz != other.bitsiz:
            raise BitsizDismatchException()

        result_value = 0
        result_dcare = 0

        if not ignore_dcare:
            mask = 1
            for idx in range(self.bitsiz):
                bit_act = mask << idx
                s_val = self.value & bit_act  # self value bit
                s_dca = self.dcare & bit_act  # self dcare bit
                o_val = other.value & bit_act  # other value bit
                o_dca = other.dcare & bit_act  # other dcare bit

                r_val = 0  # result value bit
                r_dca = 0  # result dcare bit

                if s_dca == bit_act and o_dca == bit_act:
                    r_dca = bit_act
                elif s_dca == bit_act:
                    if o_val == bit_act:
                        if not inclusive_dcare:
                            raise DcareDismatchException()
                        r_dca = bit_act
                elif o_dca == bit_act:
                    if s_val == bit_act:
                        if not inclusive_dcare:
                            raise DcareDismatchException()
                        r_dca = bit_act
                else:
                    r_val = s_val & o_val

                result_value += r_val
                result_dcare += r_dca
        else:
            result_value = self.value & other.value

        return BinValue(value=result_value, dcare=result_dcare, bitsiz=self.bitsiz)

    def logicalSub(self, other, ignore_dcare=True, inclusive_dcare=False):
        if not isinstance(other, BinValue):
            raise InvalidTypeException(varname="other", right="BinValue", wrong=type(other).__name__)
        if self.bitsiz != other.bitsiz:
            raise BitsizDismatchException()

        result_value = 0
        result_dcare = 0

        if not ignore_dcare:
            mask = 1
            for idx in range(self.bitsiz):
                bit_act = mask << idx
                s_val = self.value & bit_act  # self value bit
                s_dca = self.dcare & bit_act  # self dcare bit
                o_val = other.value & bit_act  # other value bit
                o_dca = other.dcare & bit_act  # other dcare bit

                r_val = 0  # result value bit
                r_dca = 0  # result dcare bit

                if s_dca == bit_act and o_dca == bit_act:
                    r_dca = bit_act
                elif s_dca == bit_act:
                    if not inclusive_dcare:
                        raise DcareDismatchException()
                    r_dca = bit_act
                elif o_dca == bit_act:
                    if not inclusive_dcare:
                        raise DcareDismatchException()
                    r_val = s_val
                else:
                    r_val = s_val & ~o_val

                result_value += r_val
                result_dcare += r_dca
        else:
            result_value = self.value & ~other.value

        return BinValue(value=result_value, dcare=result_dcare, bitsiz=self.bitsiz)

    def hasOneLiteral(self):
        mask = 1
        cnt = 0
        for idx in range(self.bitsiz):
            if self.value & (mask << idx):
                cnt += 1
        return cnt == 1

    @classmethod
    def parseImplicant(cls, target: str):
        literals = {}  # key: literal  value: isPrime
        last = None

        for ch in target:
            if ch == "'":
                if last is None or last not in literals.keys():
                    raise InvalidTargetStringException(val=target)
                literals[ch] = not literals[ch]
            elif ch.isalpha():
                literals[ch] = False
                last = literals[ch]
            else:
                raise InvalidTargetStringException(val=target)

        result = BinValue(value=0, bitsiz=len(literals.keys()))

        for idx, lit in enumerate(sorted(literals.keys(), reverse=True)):
            if literals[lit]:
                result.setbit(idx)

        return result

    def __str__(self) -> str:
        return f"{self.bitsiz}'b{''.join(map(lambda idx: 'x' if self.dcare & 1 << idx else '1' if self.value & 1 << idx else '0', reversed(range(self.bitsiz))))}"


# if __name__ == '__main__':
#     binValue = BinValue(value=0, bitsiz=5)
#     binValue.setbit(0)
#     print(binValue.value)
#     print(binValue.getImplicant())
#     print(binValue.hasOneLiteral())

# if __name__ == '__main__':
#     bitsiz = 4
#     a = BinValue(value=5, bitsiz=bitsiz)  # 4'b0101
#     b = BinValue(value=3, bitsiz=bitsiz)  # 4'b0011
#     print(f"a: {a}")
#     print(f"b: {b}")
#     print(f"a+b: {(a + b).value}")
#     print(f"a-b: {(a - b).value}")
#     print(f"a OR b: {a.logicalOr(b, ignore_dcare=False, inclusive_dcare=True)}")
#     print(f"a AND b: {a.logicalAnd(b, ignore_dcare=False, inclusive_dcare=True)}")
#     print(f"a SUB b: {a.logicalSub(b, ignore_dcare=False, inclusive_dcare=True)}")
#     print(f"b SUB a: {b.logicalSub(a, ignore_dcare=False, inclusive_dcare=True)}")

# if __name__ == '__main__':
#     bitsiz = 4
#     a = BinValue(value=13, dcare=4, bitsiz=bitsiz)  # 4'b1x01
#     b = BinValue(value=5, dcare=2, bitsiz=bitsiz)  # 4'b01x1
#     print(f"a: {a}")
#     print(f"b: {b}")
#     print(f"a+b: {(a + b).value}")
#     print(f"a-b: {(a - b).value}")
#     print(f"a OR b: {a.logicalOr(b, ignore_dcare=False, inclusive_dcare=True)}")
#     print(f"a AND b: {a.logicalAnd(b, ignore_dcare=False, inclusive_dcare=True)}")
#     print(f"a SUB b: {a.logicalSub(b, ignore_dcare=False, inclusive_dcare=True)}")
#     print(f"b SUB a: {b.logicalSub(a, ignore_dcare=False, inclusive_dcare=True)}")

# if __name__ == '__main__':
#     a = Implicant(binvalue=BinValue(1, bitsiz=4))
#     b = Implicant(binvalue=BinValue(3, bitsiz=4))
#     flag, result = a.combine(b)
#     print(f"a: {a}")
#     print(f"b: {b}")
#     print(f"flag: {flag}  result: {result}")

# if __name__ == '__main__':
#     table = TruthTable(in_siz=4, out_siz=1)
#     indexes = [0, 1, 2, 8, 5, 6, 9, 10, 7, 14]
#     for idx in indexes:
#         table.setValue(BinValue(idx), BinValue(1))
#     search_results = table.searchMinExprs(BinValue(1))
#     for result in search_results:
#         print(list(map(lambda x: str(x), result)))

if __name__ == '__main__':
    table = TruthTable(in_siz=4, out_siz=1)
    indexes = [2, 3, 7, 9, 11, 13]
    dcare_indexes = [1, 10, 15]
    for idx in indexes:
        table.setValue(BinValue(idx), BinValue(1))
    for idx in dcare_indexes:
        table.setValue(BinValue(idx), BinValue(1, dcare=1))
    print()
    search_results = table.searchMinExprs(BinValue(1), only_min=False)
    for result in search_results:
        print(list(map(lambda x: str(x), result)))
