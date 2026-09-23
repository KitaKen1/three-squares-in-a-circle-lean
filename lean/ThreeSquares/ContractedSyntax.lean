import ThreeSquares.PackingSyntax

/-! A tighter domain and redundant necessary conditions. Their connection to
all smaller-radius FC packings is proved in ContractedPacking.lean. -/

namespace ThreeSquares.PackingFormula

def contractedBox : RationalBox 15 :=
  fun i => if i.val < 6 then ⟨-11 / 16, 11 / 16⟩
    else if i.val < 14 then ⟨-1, 1⟩ else ⟨1 / 2, 425 / 256⟩

def centerSquared (i : Fin 3) : E :=
  .add (.square (centerX i)) (.square (centerY i))

def centerDisk (i : Fin 3) : F := le (centerSquared i) (.const (121 / 256))

def centerDistance (i j : Fin 3) : F :=
  le (.const 1) (.add (.square (sub (centerX j) (centerX i)))
    (.square (sub (centerY j) (centerY i))))

def radialMax (i : Fin 3) : F :=
  le (.add (.add (.add (centerSquared i)
    (.abs (.add (.mul (centerX i) (frame i).a) (.mul (centerY i) (frame i).c))))
    (.abs (.add (.mul (centerX i) (frame i).b) (.mul (centerY i) (frame i).d))))
    (.const (1 / 2))) (.var 14)

def contractedFormula : F :=
  .conj (centerDistance 0 1) (.conj (centerDistance 0 2) (.conj (centerDistance 1 2)
    (.conj (centerDisk 0) (.conj (centerDisk 1) (.conj (centerDisk 2)
      (.conj (radialMax 0) (.conj (radialMax 1) (.conj (radialMax 2) smallerFormula))))))))

/-- Prioritize center coordinates; this changes search order, not soundness. -/
def packingSearchWeights (i : Fin 15) : ℚ := if i.val < 6 then 4 else 1

end ThreeSquares.PackingFormula
