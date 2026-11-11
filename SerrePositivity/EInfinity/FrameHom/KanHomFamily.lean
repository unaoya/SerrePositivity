module

public import SerrePositivity.EInfinity.Hammock.ExInfinityWeakMap
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakWhitehead
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanDiagramCoherentNerve

/-!
概要：実 Hom 単体集合の全標的族を同じ Ex∞ により coherent な空間値図式にする。
方針：全族の一つの関手へ Ex∞ を後合成し、既存の Kan 図式の実現を使う。
規約：全標的と全作用素を保ち、弱自然変換を点ごとの逆へ置き換えない。
使われ方：right frame と hammock の全自然比較の coherent な実現。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{v} C]

/-- 概要：元の単体集合値の全図式を同じ Ex∞ の Kan 値図式にする。
方針：元の対象と射を同じ Ex∞ 関手で送る。
規約：全標的で一つの関手。使われ方：coherent な全族比較。 -/
def kanHomFamily (F : C ⥤ SSet.{w}) : C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{w} where
  obj X := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (F.obj X), inferInstance⟩
  map f := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (F.map f)
  map_id X := by change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (F.map (𝟙 X)) = 𝟙 _; rw [F.map_id, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map_id]
  map_comp f g := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (F.map (f ≫ g)) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (F.map f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (F.map g)
    rw [F.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map_comp]

/-- 概要：元の全自然変換を同じ Kan 化の全自然変換として公開する。
方針：同じ Ex∞ 関手を全成分に後合成する。
規約：元の全図式の自然性。使われ方：全関手 ∞ 圏の比較辺。 -/
def kanHomFamilyMap {F G : C ⥤ SSet.{w}} (η : F ⟶ G) :
    kanHomFamily F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶ kanHomFamily G ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget :=
  Functor.whiskerRight η _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity

/-- 概要：元の全 Kan 化族は各標的で Kan 複体。
方針：同じ Ex∞ の Kan 性を読む。
規約：元の標的は任意。使われ方：同じ比較の QCat 同値判定。 -/
lemma kanHomFamily_kanComplex (F : C ⥤ SSet.{w}) (X : C) :
    KanComplex ((kanHomFamily F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).obj X) := by
  change KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (F.obj X))
  infer_instance
attribute [local instance] kanHomFamily_kanComplex

/-- 概要：元の全成分が弱同値なら同じ Kan 比較の全成分は QCat 同値。
方針：Ex∞ の弱同値保存と Kan 複体の Whitehead 判定を使う。
規約：同じ元の比較射の像。使われ方：全自然変換の coherent 反転。 -/
lemma kanHomFamilyMap_isQCatEquivalence {F G : C ⥤ SSet.{w}} (η : F ⟶ G)
    (hη : ∀ X, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (η.app X)) (X : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((kanHomFamilyMap η).app X) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (η.app X))
  exact (Hammock.exInfinity_map_weak _ (hη X)).isSimplicialHomotopyEquivalence.isQCatEquivalence

/-- 概要：同じ全 Hom 族の coherent な空間値図式を回収する。
方針：元の strict Kan 値図式の実現を使う。
規約：始域は同じ nerve の宇宙持ち上げ。使われ方：関手 ∞ 圏での全族比較。 -/
def kanHomFamilyCoherent {C : Type w} [Category.{w} C] (F : C ⥤ SSet.{w}) :
    SSet.uliftFunctor.{w + 1, w}.obj (nerve C) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{w} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (kanHomFamily F)

end SerrePositivity.EInfinity.FrameHom
