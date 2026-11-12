module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementUnderEvaluation

/-!
概要：replacement 上の相対 Hom から strict な自然変換の空間へ戻す射。
方針：各 undercategory の普遍評価と相対射の普遍評価を合成し、二回 curry する。
規約：係数図式と射影の充填性は構成には要求しない。
使われ方：Kerodon Construction 5.3.4.7（Tag 026D）、Corollary 5.6.0.6（Tag 028T）、scaffold による写像空間比較の逆。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：replacement 上の相対射を、指定対象での係数値から strict transport への射の族へ戻す。
方針：under の普遍評価の後に相対評価を合成し、under の変数を相対 curry、係数を curry する。
規約：同じ相対射の空間全体をパラメーターとする。
使われ方：Kerodon Construction 5.3.1.5（Tag 035J）、Construction 5.3.4.7（Tag 026D）、逆向きの比較の対象成分。 -/
def strictDiagramScaffoldInverseComponent {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {E : SSet.{u}} (q : E ⟶ nerve C) (c : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F) ⟶
      (ihom (F.obj c)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransport q c) :=
  curry (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorCurry
    ((α_ (nerve (Under c)) (F.obj c)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F))).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementUnderEvaluation F c ▷ _) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEvaluation (Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F)) (Over.mk q)) (by
    have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEvaluation
        (Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F)) (Over.mk q) ≫ q =
        fst (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorEvaluation_projection (Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F)) (Over.mk q)
    rw [Category.assoc, Category.assoc, hp,
      ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementUnderEvaluation F c ▷ _), whiskerRight_fst,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementUnderEvaluation_projection]
    simp only [associator_inv_fst_fst_assoc]))

/-- 概要：単体集合の内部 Hom の前合成は各入力で通常の前合成に一致する。
方針：前合成を curry した評価で表し、パラメーターの恒等射との合成を消去する。
規約：全ての次数とパラメーターでの計算則。
使われ方：Kerodon §4.6.7（Tag 01LA）、strict transport の undercategory による前合成の評価。 -/
lemma sSetInternalHom_pre_app {A D E : SSet.{u}} (i : D ⟶ A)
    (n k : SimplexCategoryᵒᵖ) (s : ((ihom A).obj E).obj n) (α : n ⟶ k) (d : D.obj k) :
    ((((pre i).app E).app n s).app k α d) = s.app k α (i.app k d) := by
  rw [← curry_uncurry ((pre i).app E), uncurry_pre]
  change s.app k (α ≫ 𝟙 k) (i.app k d) = _
  rw [Category.comp_id]

/-- 概要：逆向きの対象成分を二つのパラメーターで評価する具体的な式。
方針：二回の curry を展開し、相対射の評価に残る恒等射との合成を消去する。
規約：係数の入力は内側のパラメーター β で制限する。
使われ方：Kerodon Construction 5.3.4.7（Tag 026D）、逆向きの変換の自然性と逆条件の計算。 -/
lemma strictDiagramScaffoldInverseComponent_app {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {E : SSet.{u}} (q : E ⟶ nerve C) (c : C)
    (n k l : SimplexCategoryᵒᵖ)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F)).obj n)
    (α : n ⟶ k) (y : (F.obj c).obj k) (β : k ⟶ l) (τ : (nerve (Under c)).obj l) :
    ((((strictDiagramScaffoldInverseComponent F q c).app n x).app k α y).val.app l β τ) =
      x.val.app l (α ≫ β) ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementUnderEvaluation F c).app l
        (τ, (F.obj c).map β y)) := by
  change x.val.app l ((α ≫ β) ≫ 𝟙 l)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementUnderEvaluation F c).app l (τ, (F.obj c).map β y)) = _
  rw [Category.comp_id]

/-- 概要：replacement 上の相対射を、係数図式から標的の strict transport への strict な変換の空間へ戻す。
方針：各対象で二回 curry した射を束ね、under の普遍評価の自然性で strict な自然性を示す。
規約：全次数の単体を保ち、頂点ごとの選択を使わない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict な変換の scaffold 評価に対する逆射。 -/
def strictDiagramMappingScaffoldInverse {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {E : SSet.{u}} (q : E ⟶ nerve C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportDiagram q) where
  app n := ↾fun x ↦ ⟨fun c ↦ (strictDiagramScaffoldInverseComponent F q c).app n x, by
    intro c d f k α y
    apply Subtype.ext
    apply CategoryTheory.Functor.functorHom_ext
    intro l β
    apply ConcreteCategory.hom_ext
    intro τ
    change ((((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap f)).app E).app k
      ((((strictDiagramScaffoldInverseComponent F q c).app n x).app k α y).val)).app l β τ) = _
    rw [sSetInternalHom_pre_app, strictDiagramScaffoldInverseComponent_app]
    refine Eq.trans ?_ (strictDiagramScaffoldInverseComponent_app F q d n k l x α
      ((F.map f).app k y) β τ).symm
    have hm := ConcreteCategory.congr_hom ((F.map f).naturality β) y
    change (F.map f).app l ((F.obj c).map β y) =
      (F.obj d).map β ((F.map f).app k y) at hm
    rw [← hm]
    have he := congrArg (fun h : nerve (Under d) ⊗ F.obj c ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ↦
      h.app l (τ, (F.obj c).map β y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementUnderEvaluation_naturality F f)
    exact congrArg (fun z : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F).obj l ↦ x.val.app l (α ≫ β) z) he⟩
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    funext c
    apply CategoryTheory.Functor.functorHom_ext
    intro d β
    apply ConcreteCategory.hom_ext
    intro y
    apply Subtype.ext
    apply CategoryTheory.Functor.functorHom_ext
    intro k γ
    apply ConcreteCategory.hom_ext
    intro τ
    rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
