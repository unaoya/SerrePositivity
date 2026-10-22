module

public import SerrePositivity.KST.LocalizingInvariants.CochainActionTruncationDesc
public import SerrePositivity.KST.LocalizingInvariants.BimoduleAlongEpi
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikov

/-!
概要：集中した実 dg 双加群の作用を、底代数の有限 Postnikov 切断へ降ろす。
方針：内部 Hom からの作用降下と tensor 全射性で、三つの作用則を移す。
規約：左右作用の因子分解を証明して使う。使われ方：Postnikov 拡大の係数。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A : Mon (Complex R)) [A.X.IsStrictlyLE 0]
  (M : Bimod A A) (k : ℤ) [M.X.IsStrictlyLE k] [M.X.IsStrictlyGE k] (n : ℤ) (hn : 0 ≤ n)

def postnikovBimoduleConstruction : Bimod (postnikov R A n) (postnikov R A n) := by
  let q := postnikovQuotient R A n
  have : Epi q.hom := TruncationDesc.projection_epi A.X (-n)
  have : Epi (q.hom ⊗ₘ q.hom) := TruncationDesc.tensor_epi _ _
  have : Epi (q.hom ⊗ₘ 𝟙 M.X) := TruncationDesc.tensor_epi _ _
  have : Epi (𝟙 M.X ⊗ₘ q.hom) := TruncationDesc.tensor_epi _ _
  have : Epi ((q.hom ⊗ₘ q.hom) ⊗ₘ 𝟙 M.X) := TruncationDesc.tensor_epi _ _
  have : Epi ((q.hom ⊗ₘ 𝟙 M.X) ⊗ₘ q.hom) := TruncationDesc.tensor_epi _ _
  have : Epi ((𝟙 M.X ⊗ₘ q.hom) ⊗ₘ q.hom) := TruncationDesc.tensor_epi _ _
  exact bimoduleAlongEpi q M
    (ActionDesc.left k (-n) (by omega) M.actLeft)
    (ActionDesc.right k (-n) (by omega) M.actRight)
    (ActionDesc.projection_left k (-n) (by omega) M.actLeft)
    (ActionDesc.projection_right k (-n) (by omega) M.actRight)

def postnikovBimodule : Bimod (postnikov R A n) (postnikov R A n) where
  X := M.X
  actLeft := ActionDesc.left k (-n) (by omega) M.actLeft
  actRight := ActionDesc.right k (-n) (by omega) M.actRight
  one_actLeft := (postnikovBimoduleConstruction R A M k n hn).one_actLeft
  actRight_one := (postnikovBimoduleConstruction R A M k n hn).actRight_one
  left_assoc := (postnikovBimoduleConstruction R A M k n hn).left_assoc
  right_assoc := (postnikovBimoduleConstruction R A M k n hn).right_assoc
  middle_assoc := (postnikovBimoduleConstruction R A M k n hn).middle_assoc

lemma postnikovBimodule_left_projection :
    ((postnikovQuotient R A n).hom ▷ M.X) ≫
      (postnikovBimodule R A M k n hn).actLeft = M.actLeft :=
  ActionDesc.projection_left k (-n) (by omega) M.actLeft

lemma postnikovBimodule_right_projection :
    (M.X ◁ (postnikovQuotient R A n).hom) ≫
      (postnikovBimodule R A M k n hn).actRight = M.actRight :=
  ActionDesc.projection_right k (-n) (by omega) M.actRight

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
