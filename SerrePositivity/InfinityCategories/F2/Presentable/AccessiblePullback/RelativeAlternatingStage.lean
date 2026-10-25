module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.OrdinalPrefixes
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.ComponentPrefixGluing
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.ClosedPrefixGluing
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.WellFoundedChoice
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.IndRelativePresentation

/-!
概要：元の二つの表示添字内の相対交互構成の各全前置段を記録する。
方針：固定標的の slice 内の全図式と、その両成分の元の表示図式との厳密な一致を保つ。
規約：頂点や辺だけの一致で高次整合を代用しない。
使われ方：全前置段を保持する長さ κ₀ の相対交互塔。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：各閉前置段の全交互図式と元の両表示添字への制限。
方針：固定標的の slice 内で両成分の全図式が厳密に一致する条件を保持する。
規約：存在や選択を仮定せず、再帰で構成する段の型だけを定義する。
使われ方：well-founded 選択へ渡す全前置段。 -/
structure RelativeAlternatingClosedStage (κ : Cardinal.{u})
    {B : SSet.{u + 1}} (x : (Δ[0] : SSet.{u + 1}) ⟶ B)
    (I : Fin 2 → SSet.{u})
    (P : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (I c) ⟶ sliceOver x)
    (a : AlternatingIndex κ) where
  index : ∀ c, nerve (AlternatingComponentClosed κ a c) ⟶ I c
  diagram : (SSet.uliftFunctor.{u + 1, u}).obj
    (nerve {b : AlternatingIndex κ // b ≤ a}) ⟶ sliceOver x
  component_eq : ∀ c,
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (alternatingClosedSection κ a c)) ≫ diagram =
      (SSet.uliftFunctor.{u + 1, u}).map (index c) ≫ P c

/-- 概要：全前置段の一方が他方へ厳密に制限されること。
方針：全交互図式と両成分の元の表示添字を同時に比較する。
規約：図式の等式は元の全単体上で要求する。
使われ方：well-founded 再帰と極限貼り合わせの整合関係。 -/
def RelativeAlternatingClosedStage.Restricts {κ : Cardinal.{u}}
    {B : SSet.{u + 1}} {x : (Δ[0] : SSet.{u + 1}) ⟶ B}
    {I : Fin 2 → SSet.{u}}
    {P : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (I c) ⟶ sliceOver x}
    {a b : AlternatingIndex κ}
    (s : RelativeAlternatingClosedStage κ x I P a)
    (t : RelativeAlternatingClosedStage κ x I P b) : Prop :=
  ∀ h : a ≤ b,
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (closedPrefixMap h)) ≫ t.diagram = s.diagram ∧
      ∀ c, nerveMap (alternatingComponentClosedMap h c) ≫ t.index c = s.index c

/-- 概要：追加前の全厳密前置段の相対図式。
方針：閉前置段と同じ条件を厳密下方集合上に保持する。
規約：極限段を含み、終頂点を要求しない。
使われ方：全過去段を貼り合わせて一頂点追加の相対因子化へ渡す。 -/
structure RelativeAlternatingOpenStage (κ : Cardinal.{u})
    {B : SSet.{u + 1}} (x : (Δ[0] : SSet.{u + 1}) ⟶ B)
    (I : Fin 2 → SSet.{u})
    (P : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (I c) ⟶ sliceOver x)
    (a : AlternatingIndex κ) where
  index : ∀ c, nerve (AlternatingComponentLower κ a c) ⟶ I c
  diagram : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (AlternatingLower κ a)) ⟶ sliceOver x
  component_eq : ∀ c,
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (alternatingLowerSection κ a c)) ≫ diagram =
      (SSet.uliftFunctor.{u + 1, u}).map (index c) ≫ P c

/-- 概要：整合する全過去閉前置段から、現在の全厳密前置段を構成する。
方針：全交互図式と元の成分表示添字を別々に厳密に貼り合わせ、被覆上で同じ成分を回収する。
規約：極限前置段にも終頂点や余極限を要求しない。
使われ方：well-founded 相対交互構成の各再帰段への入力。 -/
lemma exists_relativeAlternatingOpenStage {κ : Cardinal.{u}}
    {B : SSet.{u + 1}} {x : (Δ[0] : SSet.{u + 1}) ⟶ B}
    {I : Fin 2 → SSet.{u}}
    {P : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (I c) ⟶ sliceOver x}
    (a : AlternatingIndex κ)
    (prev : ∀ b : {i : AlternatingIndex κ // i < a}, RelativeAlternatingClosedStage κ x I P b.val)
    (hprev : ∀ b d : {i : AlternatingIndex κ // i < a}, b < d → (prev b).Restricts (prev d)) :
    Nonempty (RelativeAlternatingOpenStage κ x I P a) := by
  have hdiagram : ∀ (b d : {i : AlternatingIndex κ // i < a}) (h : b ≤ d),
      (SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (closedPrefixMap (I := AlternatingIndex κ) (a := b.val) (b := d.val) h)) ≫
        (prev d).diagram = (prev b).diagram := by
    intro b d h
    rcases h.lt_or_eq with h | rfl
    · exact ((hprev b d h) h.le).1
    · rfl
  have hcomponent : ∀ c, ∀ (b d : {i : AlternatingIndex κ // i < a}) (h : b ≤ d),
      nerveMap (alternatingComponentClosedMap (a := b.val) (b := d.val) h c) ≫
        (prev d).index c = (prev b).index c := by
    intro c b d h
    rcases h.lt_or_eq with h | rfl
    · exact ((hprev b d h) h.le).2 c
    · rfl
  obtain ⟨Q, hQ⟩ := exists_strictPrefixGluing a (fun b ↦ (prev b).diagram) hdiagram
  have hc : ∀ c, ∃ J : nerve (AlternatingComponentLower κ a c) ⟶ I c,
      ∀ b, nerveMap (componentClosedIntoLower a b c) ≫ J = (prev b).index c :=
    fun c ↦ exists_componentPrefixGluing a c (fun b ↦ (prev b).index c) (hcomponent c)
  choose J hJ using hc
  refine ⟨⟨J, Q, fun c ↦ ?_⟩⟩
  apply componentPrefix_ulift_hom_ext a c
  intro b
  have hm : nerveMap (componentClosedIntoLower a b c) ≫
      nerveMap (alternatingLowerSection κ a c) =
      nerveMap (alternatingClosedSection κ b.val c) ≫ nerveMap (closedPrefixIntoStrict a b) := rfl
  calc
    _ = (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (alternatingClosedSection κ b.val c)) ≫
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (closedPrefixIntoStrict a b)) ≫ Q) := by
      rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, hm,
        CategoryTheory.Functor.map_comp, Category.assoc]
    _ = (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (alternatingClosedSection κ b.val c)) ≫
        (prev b).diagram := by rw [hQ]
    _ = (SSet.uliftFunctor.{u + 1, u}).map ((prev b).index c) ≫ P c := (prev b).component_eq c
    _ = _ := by
      rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, hJ]

/-- 概要：全厳密前置図式の各頂点は元のいずれかの成分の頂点。
方針：同じ交互位置の色と元の順序段を取り出す。
規約：元の零単体を厳密に回収する。
使われ方：全前置図式の compact 頂点判定。 -/
lemma alternatingLower_vertex_component {κ : Cardinal.{u}} (a : AlternatingIndex κ)
    (v : (nerve (AlternatingLower κ a)) _⦋0⦌) :
    ∃ c : Fin 2, ∃ w : (nerve (AlternatingComponentLower κ a c)) _⦋0⦌,
      (nerveMap (alternatingLowerSection κ a c)).app (Opposite.op ⦋0⦌) w = v := by
  let i := v.obj 0
  let c := (ofLex i.val).2
  let b := (ofLex i.val).1
  have hb : toLex (b, c) < a := i.property
  refine ⟨c, ComposableArrows.mk₀ (⟨b, hb⟩ : AlternatingComponentLower κ a c), ?_⟩
  refine ComposableArrows.ext (fun j ↦ ?_) (fun _ _ ↦ Subsingleton.elim _ _)
  have hj : j = 0 := by
    apply Fin.ext
    have h := j.isLt
    change j.val < 1 at h
    change j.val = 0
    omega
  subst j
  rfl

/-- 概要：元の各表示値が compact なら、全厳密前置図式の底の各頂点も compact。
方針：元の成分の全図式との厳密な一致を指定零単体に適用する。
規約：全前置図式の余極限は要求しない。
使われ方：極限段での相対 compact 図式因子化の頂点仮定。 -/
lemma RelativeAlternatingOpenStage.vertex_isKappaCompact
    {κ μ : Cardinal.{u}} {B : SSet.{u + 1}} [Quasicategory B]
    {x : (Δ[0] : SSet.{u + 1}) ⟶ B} {I : Fin 2 → SSet.{u}}
    {P : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (I c) ⟶ sliceOver x}
    {a : AlternatingIndex κ} (s : RelativeAlternatingOpenStage κ x I P a)
    (hP : ∀ c, ∀ v : (I c) _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ
      ((P c ≫ sliceOverProjection x).app (Opposite.op ⦋0⦌) (ULift.up v)))
    (v : (nerve (AlternatingLower κ a)) _⦋0⦌) :
    Compact.IsKappaCompact.{u, u + 1} μ
      ((s.diagram ≫ sliceOverProjection x).app (Opposite.op ⦋0⦌) (ULift.up v)) := by
  obtain ⟨c, w, hw⟩ := alternatingLower_vertex_component a v
  have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) (ULift.up w)) (s.component_eq c)
  change s.diagram.app (Opposite.op ⦋0⦌)
      (ULift.up ((nerveMap (alternatingLowerSection κ a c)).app (Opposite.op ⦋0⦌) w)) =
    (P c).app (Opposite.op ⦋0⦌) (ULift.up ((s.index c).app (Opposite.op ⦋0⦌) w)) at h
  rw [hw] at h
  have h' := congrArg (fun z ↦ (sliceOverProjection x).app (Opposite.op ⦋0⦌) z) h
  exact h'.symm ▸ hP c ((s.index c).app (Opposite.op ⦋0⦌) w)

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
