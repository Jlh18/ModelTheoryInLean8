import fol
import Rings.Rings

universe u

namespace Fields

open fol
open Rings

#print set.union

#print set.insert

def MulInv : sentence RingSignature :=
begin
  unfold sentence,
  unfold presentence,

end

def FieldTheory : Theory RingSignature := set.insert (Integral) RingTheory




end Fields
