module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：外側ホーンの充填条件から辺の可逆性を導く。
方針：二次ホーンで片側逆を作り、三次ホーンで同じ辺が両側逆となることを示す。
規約：指定した辺だけの充填条件を使い、全ての辺に対する充填を仮定しない。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F）、HTT Proposition 1.2.4.3 の逆向き。

対応節は Kerodon 1.4（Tag 0039）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet SSet.Truncated
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories

/-- 概要：合成三角形の第 0 面を Yoneda の射として読む。
方針：面と Yoneda の可換性を使う。規約：二切断の三角形を元の単体集合で読む。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の三次ホーンの貼り合わせ。 -/
private lemma compStruct_yoneda_face0 {X : SSet.{u}} {x y z : X _⦋0⦌}
    {f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    {g : SSet.Truncated.Edge (X := (truncation 2).obj X) y z}
    {h : SSet.Truncated.Edge (X := (truncation 2).obj X) x z}
    (t : SSet.Truncated.Edge.CompStruct f g h) :
    stdSimplex.δ (0 : Fin 3) ≫ SSet.yonedaEquiv.symm t.simplex =
      SSet.yonedaEquiv.symm g.edge := by
  apply SSet.yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv.apply_symm_apply]
  exact t.d₀.trans (SSet.yonedaEquiv.apply_symm_apply g.edge).symm

/-- 概要：合成三角形の第 1 面を Yoneda の射として読む。
方針：面と Yoneda の可換性を使う。規約：二切断の三角形を元の単体集合で読む。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の三次ホーンの貼り合わせ。 -/
private lemma compStruct_yoneda_face1 {X : SSet.{u}} {x y z : X _⦋0⦌}
    {f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    {g : SSet.Truncated.Edge (X := (truncation 2).obj X) y z}
    {h : SSet.Truncated.Edge (X := (truncation 2).obj X) x z}
    (t : SSet.Truncated.Edge.CompStruct f g h) :
    stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm t.simplex =
      SSet.yonedaEquiv.symm h.edge := by
  apply SSet.yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv.apply_symm_apply]
  exact t.d₁.trans (SSet.yonedaEquiv.apply_symm_apply h.edge).symm

/-- 概要：合成三角形の第 2 面を Yoneda の射として読む。
方針：面と Yoneda の可換性を使う。規約：二切断の三角形を元の単体集合で読む。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の三次ホーンの貼り合わせ。 -/
private lemma compStruct_yoneda_face2 {X : SSet.{u}} {x y z : X _⦋0⦌}
    {f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    {g : SSet.Truncated.Edge (X := (truncation 2).obj X) y z}
    {h : SSet.Truncated.Edge (X := (truncation 2).obj X) x z}
    (t : SSet.Truncated.Edge.CompStruct f g h) :
    stdSimplex.δ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm t.simplex =
      SSet.yonedaEquiv.symm f.edge := by
  apply SSet.yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv.apply_symm_apply]
  exact t.d₂.trans (SSet.yonedaEquiv.apply_symm_apply f.edge).symm

/-- 概要：最後の外側ホーンの充填条件を持つ辺は片側逆の三角形を持つ。
方針：e と終点の恒等辺で二次の最後のホーンを作り、充填する。
規約：quasicategory 性はこの構成には不要。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の (3)⇒(1) の第一段階。 -/
lemma HasFinalHornFillers.nonempty_leftInverse {X : SSet.{u}} {x y : X _⦋0⦌}
    {e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y} (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.HasFinalHornFillers e) :
    Nonempty (Σ g : SSet.Truncated.Edge (X := (truncation 2).obj X) y x,
      SSet.Truncated.Edge.CompStruct g e
        (SSet.Truncated.Edge.id (X := (truncation 2).obj X) y)) := by
  let idy := SSet.Truncated.Edge.id (X := (truncation 2).obj X) y
  obtain ⟨a, ha₁, ha₀⟩ := horn₂₂.isPushout.exists_desc
    (SSet.yonedaEquiv.symm idy.edge) (SSet.yonedaEquiv.symm e.edge) (by
      rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg SSet.yonedaEquiv.symm (idy.tgt_eq.trans e.tgt_eq.symm))
  have hedge : SSet.yonedaEquiv horn₂₂.ι₁₂.{u} = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge.{u} 0 := by
    apply Subtype.ext
    decide
  have hfixed : a.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge 0) = e.edge := by
    have h := congrArg SSet.yonedaEquiv ha₀
    rw [SSet.yonedaEquiv_comp, hedge] at h
    exact h.trans (SSet.yonedaEquiv.apply_symm_apply e.edge)
  obtain ⟨F, hF⟩ := he 0 a hfixed
  change (horn 2 (2 : Fin 3)).ι ≫ F = a at hF
  have hF₁ : stdSimplex.δ 1 ≫ F = SSet.yonedaEquiv.symm idy.edge := by
    rw [← horn.ι_ι_assoc (2 : Fin 3) 1 (by decide), hF]
    exact ha₁
  have hF₀ : stdSimplex.δ 0 ≫ F = SSet.yonedaEquiv.symm e.edge := by
    rw [← horn.ι_ι_assoc (2 : Fin 3) 0 (by decide), hF]
    exact ha₀
  let s := SSet.yonedaEquiv F
  have hs₁ : X.δ 1 s = idy.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hF₁]
    exact SSet.yonedaEquiv.apply_symm_apply idy.edge
  have hs₀ : X.δ 0 s = e.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hF₀]
    exact SSet.yonedaEquiv.apply_symm_apply e.edge
  have hsrc : X.δ (1 : Fin 2) (X.δ (2 : Fin 3) s) = y := by
    have hd : X.δ (1 : Fin 2) (X.δ (2 : Fin 3) s) =
        X.δ (1 : Fin 2) (X.δ (1 : Fin 3) s) := by
      simp only [SimplicialObject.δ, ← CategoryTheory.Functor.map_comp_apply, ← op_comp]
      apply congrArg (fun α : ⦋0⦌ ⟶ ⦋2⦌ ↦ X.map α.op s)
      decide
    rw [hd, hs₁]
    exact idy.src_eq
  have htgt : X.δ (0 : Fin 2) (X.δ (2 : Fin 3) s) = x := by
    have hd : X.δ (0 : Fin 2) (X.δ (2 : Fin 3) s) =
        X.δ (1 : Fin 2) (X.δ (0 : Fin 3) s) := by
      simp only [SimplicialObject.δ, ← CategoryTheory.Functor.map_comp_apply, ← op_comp]
      apply congrArg (fun α : ⦋0⦌ ⟶ ⦋2⦌ ↦ X.map α.op s)
      decide
    rw [hd, hs₀]
    exact e.src_eq
  exact ⟨⟨X.δ 2 s, hsrc, htgt⟩, ⟨s, rfl, hs₀, hs₁⟩⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.HasFinalHornFillers export _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HasFinalHornFillers (nonempty_leftInverse)


/-- 概要：最後の外側ホーンの充填条件を持つ辺は可逆。
方針：二次ホーンで作った片側逆を三次ホーンに入れ、反対側の逆の三角形を得る。
規約：次数二と三の充填だけを使い、quasicategory 性も不要。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の (3)⇒(1)。 -/
lemma isInvertibleEdge_of_hasFinalHornFillers {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.HasFinalHornFillers e) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e := by
  obtain ⟨g, t⟩ := HasFinalHornFillers.nonempty_leftInverse he
  let fs : ∀ (j : Fin 4) (_ : j ≠ 3), (Δ[2] : SSet.{u}) ⟶ X := fun j _ ↦
    ![SSet.yonedaEquiv.symm t.simplex,
      SSet.yonedaEquiv.symm (SSet.Truncated.Edge.CompStruct.idComp e).simplex,
      SSet.yonedaEquiv.symm (SSet.Truncated.Edge.CompStruct.compId e).simplex,
      SSet.yonedaEquiv.symm t.simplex] j
  have hfs : horn.IsCompatible fs := by
    intro j k hj hk hjk
    fin_cases j <;> fin_cases k <;> first
      | exact (hj rfl).elim
      | exact (hk rfl).elim
      | exact False.elim ((show ¬ _ from by decide) hjk)
      | skip
    · exact (compStruct_yoneda_face0 t).trans
        (compStruct_yoneda_face0 (SSet.Truncated.Edge.CompStruct.idComp e)).symm
    · exact (compStruct_yoneda_face1 t).trans
        (compStruct_yoneda_face0 (SSet.Truncated.Edge.CompStruct.compId e)).symm
    · exact (compStruct_yoneda_face1 (SSet.Truncated.Edge.CompStruct.idComp e)).trans
        (compStruct_yoneda_face1 (SSet.Truncated.Edge.CompStruct.compId e)).symm
  obtain ⟨a, ha⟩ := hfs.exists_desc
  have ha₀ : horn.ι (3 : Fin 4) 0 (by decide) ≫ a = SSet.yonedaEquiv.symm t.simplex :=
    ha 0 (by decide)
  have hedge : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫
      horn.ι.{u} (3 : Fin 4) 0 (by decide)) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge.{u} 1 := by
    apply Subtype.ext
    decide
  have hfixed : a.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge 1) = e.edge := by
    have h := congrArg (fun z ↦ SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ z)) ha₀
    rw [← Category.assoc, SSet.yonedaEquiv_comp, hedge] at h
    exact h.trans ((congrArg SSet.yonedaEquiv (compStruct_yoneda_face0 t)).trans
      (SSet.yonedaEquiv.apply_symm_apply e.edge))
  obtain ⟨F, hF⟩ := he 1 a hfixed
  change (horn 3 (3 : Fin 4)).ι ≫ F = a at hF
  have hface (j : Fin 4) (hj : j ≠ 3) : stdSimplex.δ j ≫ F = fs j hj := by
    rw [← horn.ι_ι_assoc (3 : Fin 4) j hj, hF]
    exact ha j hj
  let s := SSet.yonedaEquiv F
  have hs (j : Fin 4) (hj : j ≠ 3) : X.δ j s = SSet.yonedaEquiv (fs j hj) := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hface j hj]
  have hs₀ : X.δ 0 s = t.simplex := by
    exact (hs 0 (by decide)).trans (SSet.yonedaEquiv.apply_symm_apply t.simplex)
  have hs₁ : X.δ 1 s = (SSet.Truncated.Edge.CompStruct.idComp e).simplex := by
    exact (hs 1 (by decide)).trans (SSet.yonedaEquiv.apply_symm_apply _)
  have hs₂ : X.δ 2 s = (SSet.Truncated.Edge.CompStruct.compId e).simplex := by
    exact (hs 2 (by decide)).trans (SSet.yonedaEquiv.apply_symm_apply _)
  have hd (i : Fin 3) : X.δ i (X.δ (3 : Fin 4) s) = X.δ 2 (X.δ i.castSucc s) := by
    simp only [SimplicialObject.δ, ← CategoryTheory.Functor.map_comp_apply, ← op_comp]
    apply congrArg (fun α : ⦋1⦌ ⟶ ⦋3⦌ ↦ X.map α.op s)
    fin_cases i <;> decide
  have tri : SSet.Truncated.Edge.CompStruct e g
      (SSet.Truncated.Edge.id (X := (truncation 2).obj X) x) :=
    ⟨X.δ 3 s, by
      change X.δ 2 (X.δ 3 s) = e.edge
      calc
        _ = X.δ 2 (X.δ 2 s) := hd 2
        _ = e.edge := by rw [hs₂]; exact (SSet.Truncated.Edge.CompStruct.compId e).d₂,
      by
        change X.δ 0 (X.δ 3 s) = g.edge
        calc
          _ = X.δ 2 (X.δ 0 s) := hd 0
          _ = g.edge := by rw [hs₀]; exact t.d₂,
      by
        change X.δ 1 (X.δ 3 s) = _
        calc
          _ = X.δ 2 (X.δ 1 s) := hd 1
          _ = _ := by rw [hs₁]; exact (SSet.Truncated.Edge.CompStruct.idComp e).d₂⟩
  refine ⟨⟨SSet.Truncated.HomotopyCategory.homMk g, ?_, ?_⟩⟩
  · simpa using SSet.Truncated.HomotopyCategory.homMk_comp_homMk tri
  · simpa using SSet.Truncated.HomotopyCategory.homMk_comp_homMk t

/-- 概要：辺の可逆性は最後の外側ホーンの充填条件と同値。
方針：join による順方向と二次・三次ホーンによる逆方向を組み合わせる。
規約：仮定は quasicategory 性だけで、全ての n≥2 を量化する。
使われ方：Kerodon Theorem 4.4.2.6（Tag 019F） の (1)⇔(3)。 -/
@[kerodon 019F]
lemma isInvertibleEdge_iff_hasFinalHornFillers {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.HasFinalHornFillers e :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasFinalHornFillers_of_isInvertibleEdge e, isInvertibleEdge_of_hasFinalHornFillers e⟩

/-- 概要：Kan 複体のホモトピー圏は亜群。
方針：全ての射を辺で表し、最後の外側ホーンの充填からその可逆性を示す。
規約：全ての対象間の全ての射を扱う。
使われ方：HTT Proposition 1.2.5.1、Kerodon Proposition 4.4.2.1（Tag 019D） の順方向。 -/
@[kerodon 0052, kerodon 00HZ]
instance kanComplex_ho_isGroupoid (X : SSet.{u}) [KanComplex X] :
    IsGroupoid (hoFunctor.obj X) where
  all_isIso {x y} f := by
    obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective x
    obtain ⟨y, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective y
    obtain ⟨e, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective x y f
    exact isInvertibleEdge_of_hasFinalHornFillers e (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasFinalHornFillers_of_kanComplex e)

end SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "1.2.3.4"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.kanComplex_ho_isGroupoid
attribute [cite HTT "1.2.5.3"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.kanComplex_ho_isGroupoid
