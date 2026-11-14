module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomology
public import SerrePositivity.KST.LocalizingInvariants.CochainConnectiveLift
public import SerrePositivity.KST.LocalizingInvariants.MonoidObjectAlongMono

/-!
概要：実非可換 dg 代数の smart τ≤0 に、元の単位・積を持ち上げた代数構造を構成する。
方針：非正次数からの一意な持ち上げと tensor の上界を使い、包含の単射性で三則を示す。
規約：connective cover は実モノイド対象。使われ方：有限 Postnikov 代数切断の始域。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory HomologicalComplex ComplexShape
open scoped MonObj
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra

variable (R : Type u) [CommRing R]

def coverComplex (B : Mon (Complex R)) : Complex R := B.X.truncLE 0

def coverInclusion (B : Mon (Complex R)) : coverComplex R B ⟶ B.X := B.X.ιTruncLE 0

instance coverComplex_nonpositive (B : Mon (Complex R)) : (coverComplex R B).IsStrictlyLE 0 := by
  change (HomologicalComplex.truncLE B.X (embeddingUpIntLE 0)).IsStrictlySupported _
  infer_instance

instance coverInclusion_mono (B : Mon (Complex R)) : Mono (coverInclusion R B) := by
  change Mono (HomologicalComplex.ιTruncLE B.X (embeddingUpIntLE 0))
  infer_instance

local instance coverTensor_nonpositive (B : Mon (Complex R)) :
    (coverComplex R B ⊗ coverComplex R B).IsStrictlyLE 0 :=
  ConnectiveLift.tensor_nonpositive _ _

def coverOne (B : Mon (Complex R)) : 𝟙_ (Complex R) ⟶ coverComplex R B :=
  ConnectiveLift.lift η[B.X]

def coverMul (B : Mon (Complex R)) : coverComplex R B ⊗ coverComplex R B ⟶ coverComplex R B :=
  ConnectiveLift.lift ((coverInclusion R B ⊗ₘ coverInclusion R B) ≫ μ[B.X])

lemma coverOne_inclusion (B : Mon (Complex R)) : coverOne R B ≫ coverInclusion R B = η[B.X] :=
  ConnectiveLift.lift_inclusion _

lemma coverMul_inclusion (B : Mon (Complex R)) : coverMul R B ≫ coverInclusion R B =
    (coverInclusion R B ⊗ₘ coverInclusion R B) ≫ μ[B.X] :=
  ConnectiveLift.lift_inclusion _

def connectiveCover (B : Mon (Complex R)) : Mon (Complex R) where
  X := coverComplex R B
  mon := monoidObjectAlongMono B (coverInclusion R B) (coverOne R B) (coverMul R B)
    (coverOne_inclusion R B) (coverMul_inclusion R B)

def connectiveCoverInclusion (B : Mon (Complex R)) : connectiveCover R B ⟶ B :=
  Mon.Hom.mk' (coverInclusion R B) (coverOne_inclusion R B) (coverMul_inclusion R B)

lemma connectiveCover_isConnective (B : Mon (Complex R)) :
    IsConnective R (connectiveCover R B) := by
  change (coverComplex R B).IsLE 0
  infer_instance

lemma connectiveCoverInclusion_quasiIso (B : Mon (Complex R)) (hB : IsConnective R B) :
    QuasiIso (connectiveCoverInclusion R B).hom := by
  haveI : B.X.IsLE 0 := hB
  change QuasiIso (B.X.ιTruncLE 0)
  infer_instance

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "7.1.3.13" (partial := component) "仮定：通常可換環上の厳密な非可換 dg 代数と厳密に非正次数の入力代数（Lean が強い：この dg 模型の厳密な射に限る）。結論：smart connective cover と包含を代数として構成し、非負ホモトピー次数の群の同型および厳密な連結入力からの射の一意な持ち上げを示す（存在・群の比較・通常 Hom の普遍性の部分に一致）。局所化後の全写像空間と一般 Eₖ 代数の包含の ∞ 右随伴は含まれない。"] _root_.SerrePositivity.KST.LocalizingInvariants.DGAlgebra.connectiveCover
