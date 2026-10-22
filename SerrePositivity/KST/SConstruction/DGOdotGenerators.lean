module
public import SerrePositivity.KST.SConstruction.DGAlgebraEnvelopeGenerator
public import SerrePositivity.KST.SConstruction.DGOdotGeneratorConditions

/-! # 元の実 dg 代数四角形の二自由生成条件の供給
概要：元の左右小模型の実自由代表が全 Perf を生成することを証明する。
方針：D の実小自由生成 API を元の実延長像の包絡模型へ移す。
規約：生成条件を仮定にしない。使われ方：元の実 ⊙→商の無条件 Morita 比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => dgAlgebraCategory R (DGOdotInput.source d)
local notation "C" => dgAlgebraCategory R (DGOdotInput.left d)
local notation "D" => dgAlgebraCategory R (DGOdotInput.right d)
local notation "L" => dgAlgebraMap R (DGOdotInput.top d)
local notation "G" => dgAlgebraMap R (DGOdotInput.side d)

/-- 元の四角形の左右の実自由代表は、それぞれの小模型で全 Perf を生成する。 -/
lemma dgOdotGeneratorConditions : DGOdotGeneratorConditions R d where
  left := dgAlgebraEnvelope_perfectOver_representable_eq R d.left (DGSmallPerfectBase R (A))
    (dgSmallPerfectEnvelopeExtensionFamily R (A) (C) Empty (dgSmallPerfectBaseFamily R (A)) (L))
    ((L).obj (dgOdotInputSourcePoint R d))
  right := dgAlgebraEnvelope_perfectOver_representable_eq R d.right (DGSmallPerfectBase R (A))
    (dgSmallPerfectEnvelopeExtensionFamily R (A) (D) Empty (dgSmallPerfectBaseFamily R (A)) (G))
    (dgOdotInputRightPoint R d)

end SerrePositivity.KST.SConstruction
