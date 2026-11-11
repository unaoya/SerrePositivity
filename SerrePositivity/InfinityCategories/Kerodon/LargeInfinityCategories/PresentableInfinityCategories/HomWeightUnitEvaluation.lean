module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HomWeightYonedaUnit
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FunctorCompositionEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftClassificationBaseChangeHom

/-!
概要：指定 Yoneda 単位の curry と始点固定評価を同じ関手空間の写像で比較する。
方針：関手空間の各単体で、固定した第一変数の前合成を計算する。
規約：同型や対象ごとの存在へ置き換えず、指定した全写像を使う。
使われ方：P-12 の指定 Yoneda 単位と始点固定 Hom 単位の照合。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：curry 後に第一変数を固定すると、元の全関手の同じ変数固定制限になる。
方針：各関手単体の評価式を展開し、単位射の作用を除く。
規約：quasicategory 性は不要。使われ方：指定単位の前層評価の全自然な計算。 -/
lemma functorSpaceCurryMap_evaluate_first {A B X : SSet.{u}} (a : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap A B X ≫ (ihom B).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) a) =
      (pre (lift (SSet.const a) (𝟙 B))).app X := by
  apply uncurry_injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap, uncurry_natural_right, uncurry_curry,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex]
  have hp : lift (SSet.const a) (𝟙 (B ⊗ (ihom (A ⊗ B)).obj X)) ≫
      (α_ A B ((ihom (A ⊗ B)).obj X)).inv =
        lift (SSet.const a) (𝟙 B) ▷ ((ihom (A ⊗ B)).obj X) := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [← Category.assoc, hp]
  exact (MonoidalClosed.uncurry_pre (lift (SSet.const a) (𝟙 B)) X).symm

/-- 概要：元の頂点等式で正規化した Hom 作用は、未正規化の像と異種等式で一致する。
方針：指定端点等式を消去して恒等射を除く。
規約：元の射を保持する。使われ方：curry の端点移送の表示の比較。 -/
lemma normalizedVertexHomMap_heq {X Y : SSet.{u}} (f : X ⟶ Y)
    {x y : X _⦋0⦌} {x' y' : Y _⦋0⦌}
    (hx : x' = f.app (Opposite.op ⦋0⦌) x) (hy : y' = f.app (Opposite.op ⦋0⦌) y)
    (α : (HomotopyCategory.mk x : hoFunctor.obj X) ⟶ HomotopyCategory.mk y) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.normalizedVertexHomMap f hx hy α) ((hoFunctor.map f).toFunctor.map α) := by
  subst x' y'
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.normalizedVertexHomMap, eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- 概要：指定射の curry は元の関手空間の curry による像の端点移送である。
方針：curry の定義中の型移送を異種等式へ戻す。
規約：可逆性は要求しない。使われ方：指定 Yoneda 単位の評価の Hom 計算。 -/
lemma curryFunctorHom_heq_map {A B X : SSet.{u}} {f g : A ⊗ B ⟶ X}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.curryFunctorHom α)
      ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap A B X)).toFunctor.map α) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.curryFunctorHom
  dsimp only [_root_.id]
  have hcast {T U : Sort (u + 1)} (h : T = U) (z : T) : HEq (Eq.mp h z) z := by
    cases h
    rfl
  exact hcast _ _

/-- 概要：指定射の curry は、元の端点を指定した正規化 Hom 作用と一致する。
方針：未正規化の同じ像との異種等式を二つの表示で比較する。
規約：同じ指定端点等式を使う。使われ方：curry と評価の合成則への接続。 -/
lemma curryFunctorHom_eq_normalizedMap {A B X : SSet.{u}} {f g : A ⊗ B ⟶ X}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.curryFunctorHom α = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.normalizedVertexHomMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap A B X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap_vertex f).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap_vertex g).symm α := by
  exact eq_of_heq ((curryFunctorHom_heq_map α).trans (normalizedVertexHomMap_heq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap A B X) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap_vertex f).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap_vertex g).symm α).symm)

/-- 概要：curry の第一変数評価の端点は元の固定変数制限の端点。
方針：既存の curry と評価の厳密な等式を頂点へ送る。
規約：元の f と a を保持する。使われ方：指定 Hom の評価後の正規化。 -/
lemma curryFirstRestriction_vertex {A B X : SSet.{u}}
    (f : A ⊗ B ⟶ X) (a : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (lift (SSet.const a) (𝟙 B) ≫ f) =
      ((ihom B).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) a)).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (curry f)) :=
  (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex f a)).symm

/-- 概要：指定射を curry して第一変数を評価すると、同じ指定射の固定変数制限になる。
方針：正規化 Hom 作用の合成則と全関手空間の厳密な評価公式を使う。
規約：各点の存在でなく、元の射自身の等式。
使われ方：指定 Yoneda 単位の前層評価を共同 Hom 単位の制限へ戻す。 -/
lemma curryFunctorHom_evaluate_first {A B X : SSet.{u}} {f g : A ⊗ B ⟶ X}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) (a : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.normalizedVertexHomMap ((ihom B).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) a))
      (curryFirstRestriction_vertex f a) (curryFirstRestriction_vertex g a)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.curryFunctorHom α) = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precomposeFunctorHom (lift (SSet.const a) (𝟙 B)) α := by
  rw [curryFunctorHom_eq_normalizedMap, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.normalizedVertexHomMap_comp]
  have hm : HEq
      ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap A B X ≫
        (ihom B).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) a))).toFunctor.map α)
      ((hoFunctor.map ((pre (lift (SSet.const a) (𝟙 B))).app X)).toFunctor.map α) := by
    rw [functorSpaceCurryMap_evaluate_first]
  exact eq_of_heq ((normalizedVertexHomMap_heq _ _ _ α).trans (hm.trans
    (normalizedVertexHomMap_heq ((pre (lift (SSet.const a) (𝟙 B))).app X) rfl rfl α).symm))

/-- 概要：図式の等式による指定 Hom の移送は元の射と異種等式で一致する。
方針：二つの図式の等式を消去して恒等同型を除く。
規約：指定された射を保持する。使われ方：Yoneda 単位の端点移送の除去。 -/
lemma kanFunctorHomCongr_heq {A X : SSet.{u}} {F G F' G' : A ⟶ X}
    (hF : F = F') (hG : G = G') (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr hF hG α) α := by
  subst F' G'
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr, Iso.homCongr_apply, eqToIso_refl,
    Iso.refl_inv, Iso.refl_hom, Category.id_comp, Category.comp_id]
  rfl

/-- 概要：指定 Hom の異種等式は同じ全関手による後合成で保たれる。
方針：両図式の端点等式を消去して射の等式を写す。
規約：同じ後合成関手を使う。使われ方：指定 Yoneda 単位の評価後の表示の比較。 -/
lemma postcomposeFunctorHom_heq {A X Y : SSet.{u}} (q : X ⟶ Y)
    {F G F' G' : A ⟶ X} (hF : F = F') (hG : G = G')
    {α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G} {β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F' G'} (h : HEq α β) :
    HEq ((hoFunctor.map ((ihom A).map q)).toFunctor.map α)
      ((hoFunctor.map ((ihom A).map q)).toFunctor.map β) := by
  subst F' G'
  cases eq_of_heq h
  rfl

/-- 概要：curry の評価の未正規化 Hom 作用も同じ始点固定制限と一致する。
方針：正規化 Hom の異種等式と評価の等式を一般の指定射で合成する。
規約：任意の単体集合を許す。使われ方：具体的な大きい共同 Hom の証明の分割。 -/
lemma curryFunctorHom_evaluate_heq {A B X : SSet.{u}}
    {f g : A ⊗ B ⟶ X} (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) (a : A _⦋0⦌) :
    HEq ((hoFunctor.map ((ihom B).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) a))).toFunctor.map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.curryFunctorHom α)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precomposeFunctorHom (lift (SSet.const a) (𝟙 B)) α) :=
  (normalizedVertexHomMap_heq ((ihom B).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) a))
    (curryFirstRestriction_vertex f a) (curryFirstRestriction_vertex g a)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.curryFunctorHom α)).symm.trans (curryFunctorHom_evaluate_first α a).heq

/-- 概要：curry の端点移送後の評価は元の指定射の始点固定制限。
方針：移送と後合成の異種等式を curry の厳密な評価公式へ合成する。
規約：任意の単体集合と元の射を許す。使われ方：大きな共同 Hom の定義を展開しない比較。 -/
lemma curryFunctorHomCongr_evaluate_heq {A B X : SSet.{u}}
    {f g : A ⊗ B ⟶ X} {f' g' : B ⟶ (ihom A).obj X}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) (hf : curry f = f') (hg : curry g = g')
    (a : A _⦋0⦌) :
    HEq ((hoFunctor.map ((ihom B).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) a))).toFunctor.map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr hf hg (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.curryFunctorHom α)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precomposeFunctorHom (lift (SSet.const a) (𝟙 B)) α) := by
  have hp := postcomposeFunctorHom_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) a) hf.symm hg.symm
    (kanFunctorHomCongr_heq hf hg (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.curryFunctorHom α))
  exact hp.trans ((normalizedVertexHomMap_heq
    ((ihom B).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) a))
    (curryFirstRestriction_vertex f a) (curryFirstRestriction_vertex g a)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.curryFunctorHom α)).symm.trans (curryFunctorHom_evaluate_first α a).heq)

/-- 概要：指定 Yoneda 単位は共同 Hom 単位の curry の端点移送である。
方針：指定単位の定義を一度だけ展開し、一般の移送の異種等式を使う。
規約：元の指定単位を保持する。使われ方：評価前に端点移送を切り離す。 -/
lemma homWeightYonedaUnit_heq_curry {A C : SSet.{u}}
    [Quasicategory A] [Quasicategory C] (F : A ⟶ C) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.homWeightYonedaUnit F) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.curryFunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomBifunctorUnit F)) :=
  kanFunctorHomCongr_heq rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomBifunctorDiagram_curry F F) _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
