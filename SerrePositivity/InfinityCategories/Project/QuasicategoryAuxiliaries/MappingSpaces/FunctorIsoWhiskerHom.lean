module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence

/-!
概要：関手同型の前後合成の順方向の射の計算。
方針：内部 Hom が誘導するホモトピー圏の関手を使う。
規約：元の可逆二胞体の指定された射を追跡する。
使われ方：coherent 三単体の四面の関手同型の合成則。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：関手同型の前合成の順方向の射はホモトピー圏の作用に等しい。
方針：同型の前合成の定義と恒等同型の合成を計算する。
規約：射の等式を保持し、同型の存在だけに弱めない。
使われ方：四面の指定関手同型の合成関係。 -/
lemma functorIso_precomp_hom {W X Y : SSet.{u}} {f g : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (q : W ⟶ X) :
    (e.precomp q).hom = (SSet.mapHomotopyCategory ((pre q).app Y)).map e.hom := by
  rfl
/-- 概要：関手同型の後合成の順方向の射はホモトピー圏の作用に等しい。
方針：同型の後合成の定義と恒等同型の合成を計算する。
規約：射の等式を保持し、同型の存在だけに弱めない。
使われ方：四面の指定関手同型の合成関係。 -/
lemma functorIso_postcomp_hom {X Y Z : SSet.{u}} {f g : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (q : Y ⟶ Z) :
    (e.postcomp q).hom = (SSet.mapHomotopyCategory ((ihom X).map q)).map e.hom := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp, Iso.trans_hom, eqToIso_refl, Iso.refl_symm, Iso.refl_hom,
    Category.comp_id]
  change 𝟙 _ ≫ (SSet.mapHomotopyCategory ((ihom X).map q)).map e.hom = _
  exact Category.id_comp _

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
