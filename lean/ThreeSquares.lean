import ThreeSquares.FCDefinitions
import ThreeSquares.UpperBound
import ThreeSquares.AxisAligned
import ThreeSquares.Containment
import ThreeSquares.AllAxisAligned
import ThreeSquares.LocalAlgebra
import ThreeSquares.RigidMotion
import ThreeSquares.FramedPacking
import ThreeSquares.NormalizePacking
import ThreeSquares.FrameCoordinates
import ThreeSquares.FiniteParameters
import ThreeSquares.RotatedVertices
import ThreeSquares.SquareProjection
import ThreeSquares.Separation
import ThreeSquares.SeparatorCoordinates
import ThreeSquares.VertexContainment
import ThreeSquares.FiniteConstraints
import ThreeSquares.PiecewiseLinear
import ThreeSquares.EdgeNormals
import ThreeSquares.EdgeConstraints
import ThreeSquares.Target
import ThreeSquares.RationalInterval
import ThreeSquares.IntervalExpression
import ThreeSquares.IntervalCertificate
import ThreeSquares.CertificateSearch
import ThreeSquares.PackingSyntax
import ThreeSquares.CertificateExamples
import ThreeSquares.PackingFormula
import ThreeSquares.PackingCertificate
import ThreeSquares.PackingCertificateExamples
import ThreeSquares.GeneratedCertificates
import ThreeSquares.GeneratedCertificateConnection
import ThreeSquares.CenterBounds
import ThreeSquares.LocalGeometry
import ThreeSquares.OrientedPacking
import ThreeSquares.RationalRotation
import ThreeSquares.SubcriticalRationalPacking
import ThreeSquares.RationalPackingSyntax
import ThreeSquares.RationalPackingFormula
import ThreeSquares.RationalQuadrantCover
import ThreeSquares.QuadrantSymmetry
import ThreeSquares.CenterElimination
import ThreeSquares.QuadCertificate
import ThreeSquares.QuadFast
import ThreeSquares.LocalConnection
import ThreeSquares.GlobalCertificate
import ThreeSquares.BranchSymmetry
import ThreeSquares.StrictBound
import ThreeSquares.SevenCoefficient
import ThreeSquares.RepTrees
import ThreeSquares.ContractedSyntax
import ThreeSquares.WeightedSearch
import ThreeSquares.ContractedPacking
import ThreeSquares.ContractedCertificateConnection

/-! # Formal Conjectures result: three unit squares in a circle

This library imports the actual Formal Conjectures definitions and proves the
unconditional theorem `ThreeSquares.least_three_square_packing_in_circle`:
the least radius of a circle containing three freely rotated unit squares is
`5 * sqrt 17 / 16`. The matching upper bound is explicit. For the lower bound,
the 512 signed edge-separation branches are reduced by square symmetries and
label exchange to 64 representative certificate trees (3,928 leaves total).
All trees and the branch map are checked by Lean, and the certificate assembly
proves the unrestricted bound with no extra hypotheses. The full project build,
FC declaration integration check, and 441-theorem axiom audit are automated in
`verify.py`.
-/
