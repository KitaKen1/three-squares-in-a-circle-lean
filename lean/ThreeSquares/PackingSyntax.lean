import ThreeSquares.IntervalCertificate
import Mathlib.Data.Fin.VecNotation

/-! Computable syntax shared by certificate generation and the FC connection. -/

namespace ThreeSquares.PackingFormula

abbrev E := IntervalExpr 15
abbrev F := IntervalFormula 15

structure ExprFrame where
  a : E
  b : E
  c : E
  d : E

def centerX : Fin 3 → E := ![.var 0, .var 2, .var 4]
def centerY : Fin 3 → E := ![.var 1, .var 3, .var 5]
def frame : Fin 3 → ExprFrame :=
  ![⟨.const 1, .const 0, .const 0, .const 1⟩,
    ⟨.var 6, .var 7, .var 8, .var 9⟩,
    ⟨.var 10, .var 11, .var 12, .var 13⟩]

def sub (e f : E) : E := .add e (.neg f)
def le (e f : E) : F := .nonpos (sub e f)
def eq (e f : E) : F := .zero (sub e f)

def vertex (i : Fin 3) (x y : ℚ) : E :=
  .add (.square (.add (centerX i) (.add (.mul (frame i).a (.const x))
    (.mul (frame i).b (.const y)))))
    (.square (.add (centerY i) (.add (.mul (frame i).c (.const x))
      (.mul (frame i).d (.const y)))))

def orthogonal (i : Fin 3) : F :=
  .conj (eq (.add (.square (frame i).a) (.square (frame i).c)) (.const 1))
    (.conj (eq (.add (.square (frame i).b) (.square (frame i).d)) (.const 1))
      (eq (.add (.mul (frame i).a (frame i).b) (.mul (frame i).c (frame i).d)) (.const 0)))

def vertices (i : Fin 3) : F :=
  .conj (le (vertex i (-1 / 2) (-1 / 2)) (.var 14))
    (.conj (le (vertex i (-1 / 2) (1 / 2)) (.var 14))
      (.conj (le (vertex i (1 / 2) (-1 / 2)) (.var 14))
        (le (vertex i (1 / 2) (1 / 2)) (.var 14))))

def width (i : Fin 3) (u v : E) : E :=
  .mul (.const (1 / 2)) (.add
    (.abs (.add (.mul u (frame i).a) (.mul v (frame i).c)))
    (.abs (.add (.mul u (frame i).b) (.mul v (frame i).d))))

def axis (i j : Fin 3) (u v : E) : F :=
  le (.add (width i u v) (width j u v))
    (.abs (.add (.mul u (sub (centerX j) (centerX i)))
      (.mul v (sub (centerY j) (centerY i)))))

def pair (i j : Fin 3) : F :=
  .disj (axis i j (frame i).a (frame i).c)
    (.disj (axis i j (frame i).b (frame i).d)
      (.disj (axis i j (frame j).a (frame j).c) (axis i j (frame j).b (frame j).d)))

def formula : F :=
  .conj (orthogonal 0) (.conj (orthogonal 1) (.conj (orthogonal 2)
    (.conj (vertices 0) (.conj (vertices 1) (.conj (vertices 2)
      (.conj (pair 0 1) (.conj (pair 0 2) (pair 1 2))))))))

def initialBox : RationalBox 15 := fun _ => ⟨-2, 2⟩
def smallerFormula : F :=
  .conj formula (.negative (sub (.var 14) (.const (425 / 256))))

end ThreeSquares.PackingFormula
