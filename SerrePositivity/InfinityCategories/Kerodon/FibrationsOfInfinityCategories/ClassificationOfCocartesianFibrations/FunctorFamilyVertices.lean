module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorCurryHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorParameterizedPrism

/-!
概要：関手空間への族をパラメーターの頂点で制限したときの評価の計算。
方針：関手空間への射の自然性で定値単体への評価を零単体の評価へ戻す。
規約：任意の単体集合の族を扱う。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、写像空間全体の比較射を個別の変換で評価する。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：関手空間への族の uncurry を一つのパラメーター頂点で制限すると、その頂点が表す射になる。
方針：定値単体への自然性を使い、零単体と通常の射の全単射を展開する。
規約：パラメーターは直積の右因子。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、普遍的な族の頂点での計算。 -/
lemma uncurry_at_vertex {A L E : SSet.{u}} (f : L ⟶ (ihom A).obj E) (x : L _⦋0⦌) :
    lift (𝟙 A) (SSet.const x) ≫ uncurry f =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A E).symm (f.app (Opposite.op ⦋0⦌) x) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  have h := f.naturality_apply (SimplexCategory.const d.unop ⦋0⦌ 0).op x
  change (f.app d (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x d.unop.len)).app d (𝟙 d) a = _
  exact congrArg (fun z : ((ihom A).obj E).obj d => z.app d (𝟙 d) a) h

/-- 概要：相対 curry のパラメーター頂点での値は、その頂点で制限した底上の族の相対頂点。
方針：内部 Hom の族の頂点評価と curry の往復を使う。
規約：底の図式はパラメーターに関して定値。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、写像空間の比較射を一本の変換で評価する。 -/
lemma relativeFunctorCurry_vertex {A L E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B)
    (H : A ⊗ L ⟶ E) (hH : H ≫ p = fst A L ≫ a) (x : L _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorCurry H hH).app _ x =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p a (lift (𝟙 A) (SSet.const x) ≫ H) (by
        rw [Category.assoc, hH, ← Category.assoc, lift_fst, Category.id_comp]) := by
  apply Subtype.ext
  change (curry H).app (Opposite.op ⦋0⦌) x =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (lift (𝟙 A) (SSet.const x) ≫ H)
  have h := uncurry_at_vertex (curry H) x
  rw [uncurry_curry] at h
  exact ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A E) h).trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A E).apply_symm_apply _)).symm

/-- 概要：追加パラメーター付きの prism の評価を一つのパラメーター頂点で制限する。
方針：直積の三成分で因子の並べ替えと定値射を計算する。
規約：関手の定義域 B と主パラメーター K はそのまま保つ。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、普遍的な変換の族から一本の変換を回収する。 -/
lemma functorParameterizedPrism_at_parameter {K B L E : SSet.{u}}
    (H : K ⊗ L ⟶ (ihom B).obj E) (x : L _⦋0⦌) :
    lift (𝟙 (K ⊗ B)) (SSet.const x) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism H =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorFamilyPrism (lift (𝟙 K) (SSet.const x) ≫ H) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨k, b⟩
  rfl

/-- 概要：追加パラメーターの一つの頂点を挿入する射は、元の定義域の射に自然。
方針：直積の二成分を計算する。
規約：追加パラメーター L とその頂点 x を固定する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、普遍的な持ち上げを一つの変換へ制限する計算。 -/
lemma parameterVertex_naturality {A B L : SSet.{u}} (f : A ⟶ B) (x : L _⦋0⦌) :
    lift (𝟙 A) (SSet.const x) ≫ (f ▷ L) = f ≫ lift (𝟙 B) (SSet.const x) := rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
