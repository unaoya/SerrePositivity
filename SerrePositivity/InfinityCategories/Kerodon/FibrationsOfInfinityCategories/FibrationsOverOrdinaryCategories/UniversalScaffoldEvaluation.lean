module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldUnderChain
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.LeftStrictTransportWeightedNerve

/-!
概要：strict transport の simplicial replacement の単体の対角評価。
方針：under の標準単体と係数のパラメータを対にし、相対関手の族を評価する。
規約：射影 p の left fibration 性は単体の評価の定義には不要。
使われ方：Kerodon Construction 5.3.4.7（Tag 026D）、universal scaffold の単体ごとの公式。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：相対関手の族の展開はパラメータの前合成と可換。
方針：fiber の包含を付けた後、uncurry の自然性を使う。
規約：パラメータの射の充填性は不要。
使われ方：Kerodon Construction 5.3.4.7（Tag 026D）、係数単体の制限の評価。 -/
lemma relativeFunctorUncurry_parameter {A T U E B : SSet.{u}}
    {p : E ⟶ B} {a : A ⟶ B} (f : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a) (r : U ⟶ T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (r ≫ f) = A ◁ r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry f := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry
  rw [Category.assoc, uncurry_natural_left]

/-- 概要：相対関手の前合成の族の展開は第一変数の前合成に一致する。
方針：相対前合成の包含後の公式を使って内部 Hom の計算に戻す。
規約：底の図式は第一変数の射で引き戻す。
使われ方：Kerodon Construction 5.3.4.7（Tag 026D）、始点の変化に沿う評価の自然性。 -/
lemma relativeFunctorUncurry_pre {A D T E B : SSet.{u}}
    {p : E ⟶ B} {a : A ⟶ B} (f : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p a) (i : D ⟶ A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p a i) =
      i ▷ T ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry f := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre_ι, ← Category.assoc, uncurry_pre_app]

/-- 概要：strict transport の simplicial replacement の単体を元の全空間で評価する。
方針：標準の undercategory の単体と恒等パラメータを相対関手の族へ代入する。
規約：全空間の n 単体を標準単体からの射で表示する。
使われ方：Kerodon Construction 5.3.4.7（Tag 026D）、universal scaffold の評価式。 -/
def universalScaffoldSimplex {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram p) n) :
    (Δ[n] : SSet.{u}) ⟶ E :=
  lift (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldUnderChain s.1)) (𝟙 _) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry s.2

/-- 概要：universal scaffold の単体評価は元の底の単体に重なる。
方針：相対展開の射影の式に対角の第一射影を代入する。
規約：底の単体は simplicial replacement の射列。
使われ方：Kerodon Construction 5.3.4.7（Tag 026D）、scaffold の底上の可換性。 -/
lemma universalScaffoldSimplex_projection {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram p) n) :
    universalScaffoldSimplex p s ≫ p = SSet.yonedaEquiv.symm s.1 := by
  rw [universalScaffoldSimplex, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_projection,
    ← Category.assoc, lift_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldUnderChain_yoneda_projection]

/-- 概要：universal scaffold の単体評価は単調写像による制限と可換。
方針：相対展開の二変数の自然性と under の標準単体の制限公式を使う。
規約：底の射列と係数単体を同時に制限する。
使われ方：Kerodon Construction 5.3.4.7（Tag 026D）、評価を単体集合の射へ束縛する自然性。 -/
lemma universalScaffoldSimplex_naturality {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) {m n : SimplexCategory} (α : m ⟶ n)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram p) n.len) :
    universalScaffoldSimplex p
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplexMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram p) α s) =
      stdSimplex.map α ≫ universalScaffoldSimplex p s := by
  rcases s with ⟨σ, τ⟩
  change lift (SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldUnderChain ((SimplexCategory.toCat.map α).toFunctor ⋙ σ))) (𝟙 _) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry ((stdSimplex.map α ≫ τ) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p
          (nerveMap (Under.forget (σ.obj 0)))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap (σ.map (homOfLE (Fin.zero_le (α.toOrderHom 0)))))) =
    stdSimplex.map α ≫ (lift (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldUnderChain σ)) (𝟙 _) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry τ)
  rw [relativeFunctorUncurry_pre, relativeFunctorUncurry_parameter]
  simp only [← Category.assoc, lift_whiskerRight, lift_whiskerLeft,
    Category.id_comp, Category.comp_id, comp_lift]
  exact congrArg (fun f : (Δ[m.len] : SSet.{u}) ⟶ nerve (Under (σ.obj 0)) ↦
    lift f (stdSimplex.map α) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry τ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldUnderChain_yoneda_restriction α σ).symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
