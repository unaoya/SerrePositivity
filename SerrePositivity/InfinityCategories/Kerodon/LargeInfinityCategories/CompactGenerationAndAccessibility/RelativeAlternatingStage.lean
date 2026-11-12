module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.OrdinalPrefixes
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.ComponentPrefixGluing
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.ClosedPrefixGluing
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.WellFoundedChoice
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IndRelativePresentation

/-!
概要：元の二つの表示添字内の相対交互構成の各全前置段を記録する。
方針：固定標的の slice 内の全図式と、その両成分の元の表示図式との厳密な一致を保つ。
規約：頂点や辺だけの一致で高次整合を代用しない。
使われ方：全前置段を保持する長さ κ₀ の相対交互塔。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：各閉前置段の全交互図式と元の両表示添字への制限。
方針：固定標的の slice 内で両成分の全図式が厳密に一致する条件を保持する。
規約：存在や選択を仮定せず、再帰で構成する段の型だけを定義する。
使われ方：well-founded 選択へ渡す全前置段。 -/
structure RelativeAlternatingClosedStage (κ : Cardinal.{u})
    {B : SSet.{u + 1}} (x : (Δ[0] : SSet.{u + 1}) ⟶ B)
    (I : Fin 2 → SSet.{u})
    (P : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (I c) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ) where
  index : ∀ c, nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingComponentClosed κ a c) ⟶ I c
  diagram : (SSet.uliftFunctor.{u + 1, u}).obj
    (nerve {b : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ // b ≤ a}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x
  component_eq : ∀ c,
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.alternatingClosedSection κ a c)) ≫ diagram =
      (SSet.uliftFunctor.{u + 1, u}).map (index c) ≫ P c

/-- 概要：全前置段の一方が他方へ厳密に制限されること。
方針：全交互図式と両成分の元の表示添字を同時に比較する。
規約：図式の等式は元の全単体上で要求する。
使われ方：well-founded 再帰と極限貼り合わせの整合関係。 -/
def RelativeAlternatingClosedStage.Restricts {κ : Cardinal.{u}}
    {B : SSet.{u + 1}} {x : (Δ[0] : SSet.{u + 1}) ⟶ B}
    {I : Fin 2 → SSet.{u}}
    {P : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (I c) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x}
    {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ}
    (s : RelativeAlternatingClosedStage κ x I P a)
    (t : RelativeAlternatingClosedStage κ x I P b) : Prop :=
  ∀ h : a ≤ b,
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.closedPrefixMap h)) ≫ t.diagram = s.diagram ∧
      ∀ c, nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.alternatingComponentClosedMap h c) ≫ t.index c = s.index c

/-- 概要：追加前の全厳密前置段の相対図式。
方針：閉前置段と同じ条件を厳密下方集合上に保持する。
規約：極限段を含み、終頂点を要求しない。
使われ方：全過去段を貼り合わせて一頂点追加の相対因子化へ渡す。 -/
structure RelativeAlternatingOpenStage (κ : Cardinal.{u})
    {B : SSet.{u + 1}} (x : (Δ[0] : SSet.{u + 1}) ⟶ B)
    (I : Fin 2 → SSet.{u})
    (P : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (I c) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ) where
  index : ∀ c, nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingComponentLower κ a c) ⟶ I c
  diagram : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingLower κ a)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x
  component_eq : ∀ c,
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.alternatingLowerSection κ a c)) ≫ diagram =
      (SSet.uliftFunctor.{u + 1, u}).map (index c) ≫ P c

/-- 概要：厳密前置段が指定過去の閉前置段をそのまま保持すること。
方針：全図式と両表示添字の制限を同時に比較する。
規約：全単体上の等式を要求する。
使われ方：各再帰段から全過去段への整合性の回収。 -/
def RelativeAlternatingOpenStage.Preserves {κ : Cardinal.{u}}
    {B : SSet.{u + 1}} {x : (Δ[0] : SSet.{u + 1}) ⟶ B}
    {I : Fin 2 → SSet.{u}}
    {P : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (I c) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x}
    {a : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ} (s : RelativeAlternatingOpenStage κ x I P a)
    {b : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ} (hb : b < a)
    (t : RelativeAlternatingClosedStage κ x I P b) : Prop :=
  (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.closedPrefixIntoStrict a ⟨b, hb⟩)) ≫
      s.diagram = t.diagram ∧
    ∀ c, nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.componentClosedIntoLower a ⟨b, hb⟩ c) ≫ s.index c = t.index c

/-- 概要：整合する全過去閉前置段から、現在の全厳密前置段を構成する。
方針：全交互図式と元の成分表示添字を別々に厳密に貼り合わせ、被覆上で同じ成分を回収する。
規約：極限前置段にも終頂点や余極限を要求しない。
使われ方：well-founded 相対交互構成の各再帰段への入力。 -/
lemma exists_relativeAlternatingOpenStage_preserving {κ : Cardinal.{u}}
    {B : SSet.{u + 1}} {x : (Δ[0] : SSet.{u + 1}) ⟶ B}
    {I : Fin 2 → SSet.{u}}
    {P : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (I c) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ)
    (prev : ∀ b : {i : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ // i < a}, RelativeAlternatingClosedStage κ x I P b.val)
    (hprev : ∀ b d : {i : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ // i < a}, b < d → (prev b).Restricts (prev d)) :
    ∃ s : RelativeAlternatingOpenStage κ x I P a,
      ∀ b : {i : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ // i < a}, s.Preserves b.property (prev b) := by
  have hdiagram : ∀ (b d : {i : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ // i < a}) (h : b ≤ d),
      (SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.closedPrefixMap (I := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ) (a := b.val) (b := d.val) h)) ≫
        (prev d).diagram = (prev b).diagram := by
    intro b d h
    rcases h.lt_or_eq with h | rfl
    · exact ((hprev b d h) h.le).1
    · rfl
  have hcomponent : ∀ c, ∀ (b d : {i : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ // i < a}) (h : b ≤ d),
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.alternatingComponentClosedMap (a := b.val) (b := d.val) h c) ≫
        (prev d).index c = (prev b).index c := by
    intro c b d h
    rcases h.lt_or_eq with h | rfl
    · exact ((hprev b d h) h.le).2 c
    · rfl
  obtain ⟨Q, hQ⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_strictPrefixGluing a (fun b ↦ (prev b).diagram) hdiagram
  have hc : ∀ c, ∃ J : nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingComponentLower κ a c) ⟶ I c,
      ∀ b, nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.componentClosedIntoLower a b c) ≫ J = (prev b).index c :=
    fun c ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_componentPrefixGluing a c (fun b ↦ (prev b).index c) (hcomponent c)
  choose J hJ using hc
  refine ⟨⟨J, Q, fun c ↦ ?_⟩, fun b ↦ ⟨hQ b, fun c ↦ hJ c b⟩⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.componentPrefix_ulift_hom_ext a c
  intro b
  have hm : nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.componentClosedIntoLower a b c) ≫
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.alternatingLowerSection κ a c) =
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.alternatingClosedSection κ b.val c) ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.closedPrefixIntoStrict a b) := rfl
  calc
    _ = (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.alternatingClosedSection κ b.val c)) ≫
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.closedPrefixIntoStrict a b)) ≫ Q) := by
      rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, hm,
        CategoryTheory.Functor.map_comp, Category.assoc]
    _ = (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.alternatingClosedSection κ b.val c)) ≫
        (prev b).diagram := by rw [hQ]
    _ = (SSet.uliftFunctor.{u + 1, u}).map ((prev b).index c) ≫ P c := (prev b).component_eq c
    _ = _ := by
      rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, hJ]

/-- 概要：整合する全過去閉前置段から厳密前置段が存在する。
方針：全過去段への制限を保持する貼り合わせから段を取り出す。
規約：元の二つの表示添字を保持する。
使われ方：相対一段因子化へ渡す前置図式。 -/
lemma exists_relativeAlternatingOpenStage {κ : Cardinal.{u}}
    {B : SSet.{u + 1}} {x : (Δ[0] : SSet.{u + 1}) ⟶ B}
    {I : Fin 2 → SSet.{u}}
    {P : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (I c) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ)
    (prev : ∀ b : {i : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ // i < a}, RelativeAlternatingClosedStage κ x I P b.val)
    (hprev : ∀ b d : {i : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ // i < a}, b < d → (prev b).Restricts (prev d)) :
    Nonempty (RelativeAlternatingOpenStage κ x I P a) := by
  obtain ⟨s, _⟩ := exists_relativeAlternatingOpenStage_preserving a prev hprev
  exact ⟨s⟩

/-- 概要：全厳密前置図式の各頂点は元のいずれかの成分の頂点。
方針：同じ交互位置の色と元の順序段を取り出す。
規約：元の零単体を厳密に回収する。
使われ方：全前置図式の compact 頂点判定。 -/
lemma alternatingLower_vertex_component {κ : Cardinal.{u}} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ)
    (v : (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingLower κ a)) _⦋0⦌) :
    ∃ c : Fin 2, ∃ w : (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingComponentLower κ a c)) _⦋0⦌,
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.alternatingLowerSection κ a c)).app (Opposite.op ⦋0⦌) w = v := by
  let i := v.obj 0
  let c := (ofLex i.val).2
  let b := (ofLex i.val).1
  have hb : toLex (b, c) < a := i.property
  refine ⟨c, ComposableArrows.mk₀ (⟨b, hb⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingComponentLower κ a c), ?_⟩
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
    {P : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (I c) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x}
    {a : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ} (s : RelativeAlternatingOpenStage κ x I P a)
    (hP : ∀ c, ∀ v : (I c) _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
      ((P c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x).app (Opposite.op ⦋0⦌) (ULift.up v)))
    (v : (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingLower κ a)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
      ((s.diagram ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x).app (Opposite.op ⦋0⦌) (ULift.up v)) := by
  obtain ⟨c, w, hw⟩ := alternatingLower_vertex_component a v
  have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) (ULift.up w)) (s.component_eq c)
  change s.diagram.app (Opposite.op ⦋0⦌)
      (ULift.up ((nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.alternatingLowerSection κ a c)).app (Opposite.op ⦋0⦌) w)) =
    (P c).app (Opposite.op ⦋0⦌) (ULift.up ((s.index c).app (Opposite.op ⦋0⦌) w)) at h
  rw [hw] at h
  have h' := congrArg (fun z ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x).app (Opposite.op ⦋0⦌) z) h
  exact h'.symm ▸ hP c ((s.index c).app (Opposite.op ⦋0⦌) w)

/-- 概要：閉前置段が元の厳密前置段をそのまま保持すること。
方針：全交互図式と両成分表示添字の旧境界を同時に比較する。
規約：頂点だけでなく元の全単体を保持する。
使われ方：実際の一段因子化を全相対塔の次の段へ戻す。 -/
def RelativeAlternatingClosedStage.ExtendsOpen {κ : Cardinal.{u}}
    {B : SSet.{u + 1}} {x : (Δ[0] : SSet.{u + 1}) ⟶ B}
    {I : Fin 2 → SSet.{u}}
    {P : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (I c) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x}
    {a : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ}
    (s : RelativeAlternatingClosedStage κ x I P a)
    (t : RelativeAlternatingOpenStage κ x I P a) : Prop :=
  (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.strictPrefixToClosed a)) ≫ s.diagram = t.diagram ∧
    ∀ c, nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.alternatingComponentLowerToClosed κ a c) ≫ s.index c = t.index c

/-- 概要：旧厳密前置段を保つ一段追加は、そこで保持した全過去段も保つ。
方針：元の二つの包含を合成して全図式と両表示添字を比較する。
規約：過去段への制限は元の厳密な全射の等式。
使われ方：well-founded 選択に渡す全過去段への延長条件。 -/
lemma RelativeAlternatingClosedStage.restricts_of_extendsOpen {κ : Cardinal.{u}}
    {B : SSet.{u + 1}} {x : (Δ[0] : SSet.{u + 1}) ⟶ B}
    {I : Fin 2 → SSet.{u}}
    {P : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (I c) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x}
    {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ} {s : RelativeAlternatingClosedStage κ x I P a}
    {t : RelativeAlternatingOpenStage κ x I P a}
    {r : RelativeAlternatingClosedStage κ x I P b} (hb : b < a)
    (hst : s.ExtendsOpen t) (htr : t.Preserves hb r) : r.Restricts s := by
  intro h
  constructor
  · calc
      _ = (SSet.uliftFunctor.{u + 1, u}).map
          (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.closedPrefixIntoStrict a ⟨b, hb⟩)) ≫
          ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.strictPrefixToClosed a)) ≫ s.diagram) := rfl
      _ = _ := by rw [hst.1]; exact htr.1
  · intro c
    calc
      _ = nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.componentClosedIntoLower a ⟨b, hb⟩ c) ≫
          (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.alternatingComponentLowerToClosed κ a c) ≫ s.index c) := rfl
      _ = _ := by rw [hst.2 c]; exact htr.2 c

/-- 概要：実際の一段延長から全過去段を保つ全相対交互塔を組み立てる。
方針：全過去段を厳密前置段へ貼り合わせ、指定された一段延長を well-founded 選択へ渡す。
規約：本補題は塔の組み立て。実際の一段延長の存在は別途構成する。
使われ方：相対因子化と一頂点追加の形状比較を完成した後の全塔の回収。 -/
lemma exists_relativeAlternatingTower_of_extension {κ : Cardinal.{u}}
    {B : SSet.{u + 1}} {x : (Δ[0] : SSet.{u + 1}) ⟶ B}
    {I : Fin 2 → SSet.{u}}
    {P : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (I c) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x}
    (step : ∀ a, ∀ s : RelativeAlternatingOpenStage κ x I P a,
      ∃ t : RelativeAlternatingClosedStage κ x I P a, t.ExtendsOpen s) :
    ∃ T : ∀ a, RelativeAlternatingClosedStage κ x I P a,
      ∀ a b, a < b → (T a).Restricts (T b) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_wellFounded_coherentChoice (I := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ) wellFounded_lt
    (fun a ↦ RelativeAlternatingClosedStage κ x I P a) RelativeAlternatingClosedStage.Restricts
  intro a prev hprev
  let f := fun b : {i : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ // i < a} ↦ prev b.val b.property
  have hf : ∀ b d : {i : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ // i < a}, b < d → (f b).Restricts (f d) := by
    intro b d hbd
    exact hprev b.val d.val b.property d.property hbd
  obtain ⟨s, hs⟩ := exists_relativeAlternatingOpenStage_preserving a f hf
  obtain ⟨t, ht⟩ := step a s
  exact ⟨t, fun b hb ↦ t.restricts_of_extendsOpen hb ht (hs ⟨b, hb⟩)⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
