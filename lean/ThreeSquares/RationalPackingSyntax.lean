import ThreeSquares.IntervalCertificate
import Mathlib.Data.Fin.VecNotation

/-! # Eight-variable syntax for rationally parameterized square packings

Variables 0--5 are the three centers and variables 6--7 are the rational
rotation parameters of squares 1 and 2. Square 0 has parameter zero. All
positive denominators are cleared, so the checker sees only rational
constants, polynomial operations, and absolute values.
-/

namespace ThreeSquares.RationalPackingFormula

abbrev E := IntervalExpr 8
abbrev F := IntervalFormula 8

def sub (e f : E) : E := .add e (.neg f)
def le (e f : E) : F := .nonpos (sub e f)

def centerX : Fin 3 → E := ![.var 0, .var 2, .var 4]
def centerY : Fin 3 → E := ![.var 1, .var 3, .var 5]
def parameter : Fin 3 → E := ![.const 0, .var 6, .var 7]

def denominator (i : Fin 3) : E := .add (.const 1) (.square (parameter i))
def cosineNumerator (i : Fin 3) : E := sub (.const 1) (.square (parameter i))
def sineNumerator (i : Fin 3) : E := .mul (.const 2) (parameter i)

/-- Squared vertex numerator after multiplying both coordinates by
`1 + tᵢ²`. -/
def vertexNumerator (i : Fin 3) (x y : ℚ) : E :=
  .add
    (.square (.add (.mul (denominator i) (centerX i))
      (.add (.mul (cosineNumerator i) (.const x))
        (.neg (.mul (sineNumerator i) (.const y))))))
    (.square (.add (.mul (denominator i) (centerY i))
      (.add (.mul (sineNumerator i) (.const x))
        (.mul (cosineNumerator i) (.const y)))))

def strictVertex (i : Fin 3) (x y : ℚ) : F :=
  .negative (sub (vertexNumerator i x y)
    (.mul (.const (425 / 256)) (.square (denominator i))))

def vertices (i : Fin 3) : F :=
  .conj (strictVertex i (-1 / 2) (-1 / 2))
    (.conj (strictVertex i (-1 / 2) (1 / 2))
      (.conj (strictVertex i (1 / 2) (-1 / 2))
        (strictVertex i (1 / 2) (1 / 2))))

/-- Numerator of twice the projection half-width after the frame denominator
has been removed. The supplied `(u,v)` is an axis numerator. -/
def widthNumerator (i : Fin 3) (u v : E) : E :=
  .add
    (.abs (.add (.mul u (cosineNumerator i)) (.mul v (sineNumerator i))))
    (.abs (.add (.neg (.mul u (sineNumerator i)))
      (.mul v (cosineNumerator i))))

def centerProjectionNumerator (i j : Fin 3) (u v : E) : E :=
  .add (.mul u (sub (centerX j) (centerX i)))
    (.mul v (sub (centerY j) (centerY i)))

/-- An edge-axis inequality after multiplying by the positive product of all
frame denominators. -/
def axis (i j : Fin 3) (u v : E) : F :=
  le
    (.add (.mul (widthNumerator i u v) (denominator j))
      (.mul (widthNumerator j u v) (denominator i)))
    (.mul (.const 2) (.mul (.abs (centerProjectionNumerator i j u v))
      (.mul (denominator i) (denominator j))))

def pair (i j : Fin 3) : F :=
  .disj (axis i j (cosineNumerator i) (sineNumerator i))
    (.disj (axis i j (.neg (sineNumerator i)) (cosineNumerator i))
      (.disj (axis i j (cosineNumerator j) (sineNumerator j))
        (axis i j (.neg (sineNumerator j)) (cosineNumerator j))))

def parameterBounds (i : Fin 3) : F :=
  .conj (.nonpos (.neg (parameter i)))
    (.nonpos (sub (parameter i) (.const 1)))

/-- Complete radius-free formula for the normalized three-square problem. -/
def formula : F :=
  .conj (parameterBounds 1) (.conj (parameterBounds 2)
    (.conj (vertices 0) (.conj (vertices 1) (.conj (vertices 2)
      (.conj (pair 0 1) (.conj (pair 0 2) (pair 1 2)))))))

/-- Contracted center range together with the exact parameter range. -/
def initialBox : RationalBox 8 := ![
  ⟨-11 / 16, 11 / 16⟩, ⟨-11 / 16, 11 / 16⟩,
  ⟨-11 / 16, 11 / 16⟩, ⟨-11 / 16, 11 / 16⟩,
  ⟨-11 / 16, 11 / 16⟩, ⟨-11 / 16, 11 / 16⟩,
  ⟨0, 1⟩, ⟨0, 1⟩]

end ThreeSquares.RationalPackingFormula
