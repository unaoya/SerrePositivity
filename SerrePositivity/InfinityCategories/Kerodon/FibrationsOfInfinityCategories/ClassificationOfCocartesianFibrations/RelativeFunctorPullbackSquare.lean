module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorSquarePost

/-!
概要：引き戻し四角形による相対後合成は相対写像空間の同型。
方針：相対評価を四角形の普遍性で持ち上げ、両射影で往復を検証する。
規約：fibration 性や底の充填性は不要。通常の単体集合の同型。
使われ方：Kerodon Example 5.6.2.9（Tag 026S）、unstraightening の自然性の比較射の可逆性。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：引き戻し四角形の相対後合成の逆射。
方針：写された底の図式を持つ族を四角形の普遍性で持ち上げて curry する。
規約：h の上辺が全空間の射 f、下辺が底の射 k。
使われ方：Kerodon Remark 5.6.2.18（Tag 0271）、相対写像空間の底変換の逆向きの作用。 -/
noncomputable def relativeFunctorSquareLift {A E F B D : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ D) (k : B ⟶ D) (f : E ⟶ F)
    (h : IsPullback f p q k) (a : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q (a ≫ k) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorCurry
    (h.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q (a ≫ k))))
      (fst A _ ≫ a) (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_projection, Category.assoc]))
    (h.lift_snd _ _ _)

/-- 概要：引き戻し四角形への相対持ち上げの評価の上辺への合成は元の族。
方針：パラメーター自然性と引き戻しの普遍持ち上げの第一射影を使う。
規約：任意のパラメーター T からの族に適用する。
使われ方：Kerodon §5.6.2（Tag 026H）、相対後合成と持ち上げの往復の計算。 -/
lemma relativeFunctorSquareLift_uncurry_fst {A E F B D T : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ D) (k : B ⟶ D) (f : E ⟶ F)
    (h : IsPullback f p q k) (a : A ⟶ B)
    (g : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q (a ≫ k)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (g ≫ relativeFunctorSquareLift p q k f h a) ≫ f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry g := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorUncurry_naturality, relativeFunctorSquareLift,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_curry, Category.assoc, h.lift_fst]
  have hg := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorUncurry_naturality (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q (a ≫ k))) g
  simpa only [Category.comp_id] using hg.symm

/-- 概要：引き戻し四角形は相対写像空間の同型を誘導する。
方針：後合成と普遍持ち上げを逆射とし、評価の二射影で往復を判定する。
規約：同型の順方向は可換四角形の相対後合成そのもの。
使われ方：Kerodon §5.6.2（Tag 026H）、分類の自然性に現れる相対比較射の同型。 -/
noncomputable def relativeFunctorPullbackSquareIso {A E F B D : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ D) (k : B ⟶ D) (f : E ⟶ F)
    (h : IsPullback f p q k) (a : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q (a ≫ k) where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorSquarePost p q k f h.w a
  inv := relativeFunctorSquareLift p q k f h a
  hom_inv_id := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective
    apply h.hom_ext
    · rw [relativeFunctorSquareLift_uncurry_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorSquarePost,
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_curry]
    · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_projection, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_projection]
  inv_hom_id := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorSquarePost_uncurry, relativeFunctorSquareLift,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_curry, h.lift_fst]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
