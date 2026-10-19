module

public import SerrePositivity.KST.DerivedGeometry.KInjectiveLocalizationAdjunction
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
概要：非有界局所化の K-injective 右随伴の余単位は同型で、単位は局所化で同型になる。
方針：余単位を構成した模型の比較同型と同定し、三角恒等式を用いる。
規約：随伴の構成と同じ選択を使う。
使われ方：TT §3・§8、Toën §3.2、Stacks 19.12.6 の関手的な導来分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w v u
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable (C : Type u) [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  [HasDerivedCategory.{v} C]

/--
概要：局所化随伴の余単位は選んだ K-injective 模型の標準比較。
方針：Hom 同値から作る随伴の余単位を計算する。
規約：構成した随伴についての実際の等式。
使われ方：TT §3、Toën §3.2 の導来分解の比較。
-/
lemma kInjectiveLocalizationAdjunction_counit (Y : DerivedCategory C) :
    (kInjectiveLocalizationAdjunction C).counit.app Y =
      (kInjectiveLocalizationObjectIso C Y).hom := by
  rw [kInjectiveLocalizationAdjunction, Adjunction.adjunctionOfEquivRight_counit_app]
  simp only [kInjectiveLocalizationHomEquiv, Equiv.symm_trans_apply, Equiv.symm_symm,
    Equiv.ofBijective_apply]
  change 𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) ≫ (kInjectiveLocalizationObjectIso C Y).hom = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]

/--
概要：局所化随伴の余単位は全対象で同型。
方針：実際の比較同型との等式を使う。
規約：非有界導来対象。
使われ方：TT §3、Toën §3.2 の右随伴の完全忠実性。
-/
instance kInjectiveLocalizationAdjunction_counit_isIso (Y : DerivedCategory C) :
    IsIso ((kInjectiveLocalizationAdjunction C).counit.app Y) := by
  rw [kInjectiveLocalizationAdjunction_counit]
  infer_instance

/--
概要：局所化随伴の単位は局所化後に同型。
方針：余単位の同型性と左三角恒等式を使う。
規約：任意のホモトピー対象。
使われ方：TT §3、Toën §3.2 の関手的な準同型分解。
-/
instance kInjectiveLocalizationAdjunction_map_unit_isIso (X : HomotopyCategory C (.up ℤ)) :
    IsIso (DerivedCategory.Qh.map ((kInjectiveLocalizationAdjunction C).unit.app X)) := by
  have : IsIso (DerivedCategory.Qh.map ((kInjectiveLocalizationAdjunction C).unit.app X) ≫
      (kInjectiveLocalizationAdjunction C).counit.app (DerivedCategory.Qh.obj X)) := by
    have ht : DerivedCategory.Qh.map ((kInjectiveLocalizationAdjunction C).unit.app X) ≫
        (kInjectiveLocalizationAdjunction C).counit.app (DerivedCategory.Qh.obj X) = 𝟙 _ :=
      (kInjectiveLocalizationAdjunction C).left_triangle_components X
    rw [ht]
    infer_instance
  exact IsIso.of_isIso_comp_right
    (DerivedCategory.Qh.map ((kInjectiveLocalizationAdjunction C).unit.app X))
    ((kInjectiveLocalizationAdjunction C).counit.app (DerivedCategory.Qh.obj X))

end SerrePositivity.KST.DerivedGeometry
