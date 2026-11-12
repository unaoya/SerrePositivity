module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.StrictDiagramMappingEvaluation

/-!
概要：undercategory と係数値から simplicial replacement への普遍的な評価。
方針：under の射列を底へ射影し、係数を最初の構造射で移す。
規約：通常の単体集合とその射だけを構成する。
使われ方：Kerodon Construction 5.3.2.1（Tag 035V）、Construction 5.3.4.7（Tag 026D）、strict transport の写像空間比較の逆。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：c の undercategory の射列と F(c) の単体から replacement の単体を作る。
方針：under の最初の構造射で係数を運び、射列の始点における係数にする。
規約：c は任意の底の対象。
使われ方：Kerodon Construction 5.3.2.1（Tag 035V）、相対射から strict な自然変換を回収する普遍評価。 -/
def simplicialReplacementUnderEvaluation {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) : nerve (Under c) ⊗ F.obj c ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F where
  app _ := ↾fun ⟨τ, x⟩ ↦
    ⟨τ ⋙ Under.forget c, SSet.yonedaEquiv.symm x ≫ F.map (τ.obj 0).hom⟩
  naturality := by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
    apply ConcreteCategory.hom_ext
    rintro ⟨τ, x⟩
    change ComposableArrows (Under c) n at τ
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    change SSet.yonedaEquiv.symm ((F.obj c).map α x) ≫ F.map (τ.obj (α.unop.toOrderHom 0)).hom =
      stdSimplex.map α.unop ≫ (SSet.yonedaEquiv.symm x ≫ F.map (τ.obj 0).hom) ≫
        F.map ((τ.map (homOfLE (Fin.zero_le (α.unop.toOrderHom 0)))).right)
    have hα : SSet.yonedaEquiv.symm ((F.obj c).map α x) =
        stdSimplex.map α.unop ≫ SSet.yonedaEquiv.symm x :=
      (SSet.yonedaEquiv_symm_naturality_left α.unop x).symm
    rw [hα]
    simp only [Category.assoc, ← F.map_comp]
    rw [(τ.map (homOfLE (Fin.zero_le (α.unop.toOrderHom 0)))).w]

/-- 概要：under の普遍評価は底の射列の忘却を被覆する。
方針：replacement の底の成分だけを計算する。
規約：係数値のパラメーターを第一射影で忘れる。
使われ方：Kerodon Construction 5.3.2.1（Tag 035V）、普遍評価を相対 Hom の curry に用いる底の条件。 -/
lemma simplicialReplacementUnderEvaluation_projection {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) :
    simplicialReplacementUnderEvaluation F c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F =
      fst (nerve (Under c)) (F.obj c) ≫ nerveMap (Under.forget c) := rfl

/-- 概要：under の普遍評価は底の射に関する係数の輸送と undercategory の前合成で可換。
方針：最初の構造射の合成と F の合成則を使って二つの係数単体を比較する。
規約：f は c から d への任意の射。
使われ方：Kerodon Construction 5.3.1.5（Tag 035J）、Construction 5.3.2.1（Tag 035V）、回収する変換の strict な自然性。 -/
lemma simplicialReplacementUnderEvaluation_naturality
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) {c d : C} (f : c ⟶ d) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.nerveUnderMap f ▷ F.obj c) ≫ simplicialReplacementUnderEvaluation F c =
      (nerve (Under d) ◁ F.map f) ≫ simplicialReplacementUnderEvaluation F d := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨τ, x⟩
  change ComposableArrows (Under d) n at τ
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  change SSet.yonedaEquiv.symm x ≫ F.map (f ≫ (τ.obj 0).hom) =
    SSet.yonedaEquiv.symm ((F.map f).app (Opposite.op ⦋n⦌) x) ≫ F.map (τ.obj 0).hom
  rw [F.map_comp, ← Category.assoc]
  exact congrArg (fun z ↦ z ≫ F.map (τ.obj 0).hom)
    (SSet.yonedaEquiv_symm_comp x (F.map f))

/-- 概要：標準の scaffold の under 射列を普遍評価すると元の replacement の単体を得る。
方針：最初の構造射が恒等射であることと係数図式の恒等則を使う。
規約：係数単体は Yoneda の逆で表示する。
使われ方：Kerodon Construction 5.3.4.7（Tag 026D）、scaffold 評価の逆条件の計算。 -/
lemma simplicialReplacementUnderEvaluation_scaffold {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) {n : ℕ} (σ : ComposableArrows C n) (x : (F.obj (σ.obj 0)) _⦋n⦌) :
    (simplicialReplacementUnderEvaluation F (σ.obj 0)).app (Opposite.op ⦋n⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldUnderChain σ, x) = ⟨σ, SSet.yonedaEquiv.symm x⟩ := by
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  change SSet.yonedaEquiv.symm x ≫ F.map (σ.map (𝟙 (0 : Fin (n + 1)))) = _
  rw [σ.map_id, F.map_id, Category.comp_id]

/-- 概要：under の任意の射列は、忘却した射列の標準持ち上げを最初の構造射で前合成して復元できる。
方針：各対象で under の可換三角形を用い、射は忘却関手の忠実性で比較する。
規約：射列の長さと始点 c は任意。
使われ方：Kerodon Construction 5.3.4.7（Tag 026D）、strict な変換側の scaffold 比較の逆条件。 -/
lemma scaffoldUnderChain_forget_factorization {C : Type u} [Category.{u} C]
    {c : C} {n : ℕ} (τ : ComposableArrows (Under c) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldUnderChain (τ ⋙ Under.forget c) ⋙ Under.map (τ.obj 0).hom = τ := by
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) ?_
  · change Under.mk ((τ.obj 0).hom ≫ (τ.map (homOfLE (Fin.zero_le i))).right) =
      Under.mk (τ.obj i).hom
    rw [(τ.map (homOfLE (Fin.zero_le i))).w]
  · intro i j f
    apply (Under.forget c).map_injective
    simp
    rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
