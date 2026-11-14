module

public meta import SerrePositivity.Util.Citation
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
local notation "A" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.source d)
local notation "C" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.left d)
local notation "D" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.right d)
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.top d)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.side d)

/-- 元の四角形の左右の実自由代表は、それぞれの小模型で全 Perf を生成する。 -/
lemma dgOdotGeneratorConditions : DGOdotGeneratorConditions R d where
  left := dgAlgebraEnvelope_perfectOver_representable_eq R d.left (DGSmallPerfectBase R (A))
    (dgSmallPerfectEnvelopeExtensionFamily R (A) (C) Empty (dgSmallPerfectBaseFamily R (A)) (L))
    ((L).obj (dgOdotInputSourcePoint R d))
  right := dgAlgebraEnvelope_perfectOver_representable_eq R d.right (DGSmallPerfectBase R (A))
    (dgSmallPerfectEnvelopeExtensionFamily R (A) (D) Empty (dgSmallPerfectBaseFamily R (A)) (G))
    (dgOdotInputRightPoint R d)

end SerrePositivity.KST.SConstruction

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite LT "Def 1.8" (partial := component) "仮定：指定 dg 代数とその小 perfect 模型（Lean が強い）。結論：左右の自由代表の生成性を個別に述べる。任意集合 S が任意の Cat^perf を生成する一般定義の範囲より狭い（Lean が弱い）。"] _root_.SerrePositivity.KST.SConstruction.dgOdotGeneratorConditions
