module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Edges

/-!
概要：coherent nerve の一単体から通常の射を取り出す。
方針：二点の thickening の始点から終点への path で豊穣 Hom の零単体を評価する。
規約：局所 Kan 性を仮定せず、端点も含む依存和として記録する。
使われ方：Kerodon §2.4.3（Tag 00KM）、Remark 3.1.6.3（Tag 01YZ）、pointed-space fiber の頂点比較。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：二点の thickening の始点から終点への標準 path。
方針：二点の全体集合を使う。
規約：頂点は ULift (Fin 2) の 0 と 1。
使われ方：Kerodon §2.4.3（Tag 00KM）、一単体の豊穣 Hom の評価。 -/
def coherentOnePath : SimplicialThickening.Path
    (ULift.up (0 : Fin 2) : ULift.{u} (Fin 2)) (ULift.up (1 : Fin 2)) where
  I := Set.univ
  left_le k _ := Fin.zero_le k.down
  le_right k _ := Fin.le_last k.down

/-- 概要：coherent nerve の一単体の始点・終点と通常の射。
方針：標準 path の零単体の像を通常の射との同値で読む。
規約：対象が変わるため、結果は二つの端点を含む依存和。
使われ方：Kerodon Remark 3.1.6.3（Tag 01YZ）、coherent な辺から通常の射への復元。 -/
noncomputable def coherentNerveArrowData {C : Type v} [Category.{u} C]
    [SimplicialCategory C] (s : (SimplicialNerve C) _⦋1⦌) : Σ X Y : C, X ⟶ Y :=
  ⟨s.obj ⟨ULift.up 0⟩, s.obj ⟨ULift.up 1⟩,
    (SimplicialCategory.homEquiv' _ _).symm
      ((s.map ⟨ULift.up 0⟩ ⟨ULift.up 1⟩).app (Opposite.op ⦋0⦌)
        (ComposableArrows.mk₀ coherentOnePath))⟩

/-- 概要：通常の射から作った一単体の射データは元の射データ。
方針：標準 path の像と定値零単体を計算し、豊穣 Hom の同値の逆写像則を使う。
規約：一単体の表示は nerveToCoherent を使う。
使われ方：Kerodon Remark 3.1.6.3（Tag 01YZ）、通常の射を coherent nerve に埋めた場合の計算。 -/
lemma coherentNerveArrowData_of_arrow {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} (f : X ⟶ Y) :
    coherentNerveArrowData
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f)) = ⟨X, Y, f⟩ := by
  change (⟨X, Y, (SimplicialCategory.homEquiv' X Y).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' X Y f) 0)⟩ : Σ X Y : C, X ⟶ Y) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero, Equiv.symm_apply_apply]

/-- 概要：二点の thickening の同じ端点間の path は高々一つ。
方針：二点の間の点は必ず端点のどちらかであり、path は両端点を含む。
規約：逆向きの場合の空の型も含む。
使われ方：Kerodon §2.4.3（Tag 00KM）、coherent nerve の一単体の復元の一意性。 -/
instance coherentOnePath_subsingleton (i j : ULift.{u} (Fin 2)) :
    Subsingleton (SimplicialThickening.Path i j) := by
  constructor
  intro P Q
  apply SimplicialThickening.Path.ext
  ext k
  have endpoint (R : SimplicialThickening.Path i j) (hk : k ∈ R.I) : k = i ∨ k = j := by
    have hl := R.left_le k hk
    have hr := R.le_right k hk
    change i.down ≤ k.down at hl
    change k.down ≤ j.down at hr
    by_cases h : k.down.val = i.down.val
    · exact Or.inl (ULift.ext (Fin.ext h))
    · exact Or.inr (ULift.ext (Fin.ext (by
        have := i.down.isLt
        have := j.down.isLt
        have := k.down.isLt
        omega)))
  constructor
  · intro hk
    rcases endpoint P hk with rfl | rfl
    · exact Q.left
    · exact Q.right
  · intro hk
    rcases endpoint Q hk with rfl | rfl
    · exact P.left
    · exact P.right

/-- 概要：二点の thickening の豊穣 Hom の単体は定値単体。
方針：path の一意性で順序図式を定値図式と比較する。
規約：path が存在する場合だけ入力の単体が存在する。
使われ方：Kerodon §2.4.3（Tag 00KM）、一単体が通常の射から復元できることの準備。 -/
lemma coherentOneHom_simplex_constant (i j : ULift.{u} (Fin 2)) (n : ℕ)
    (P : (nerve (SimplicialThickening.Path i j)) _⦋n⦌) :
    P = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (ComposableArrows.mk₀ (P.obj 0)) n := by
  apply CategoryTheory.Functor.ext (fun _ ↦ Subsingleton.elim _ _)

/-- 概要：二点の thickening の各対象の豊穣恒等は全射。
方針：端点の等しい path の一意性で nerve の全単体を恒等の像にする。
規約：始点・終点のいずれにも適用できる。
使われ方：Kerodon §2.4.3（Tag 00KM）、一単体の対角 Hom の一意性。 -/
lemma coherentOne_eId_epi (o : SimplicialThickening (ULift.{u} (Fin 2))) :
    Epi (eId SSet o) := by
  let : Subsingleton (o ⟶ o) := coherentOnePath_subsingleton o.as o.as
  rw [NatTrans.epi_iff_epi_app]
  intro n
  rw [epi_iff_surjective]
  intro F
  refine ⟨PUnit.unit, ?_⟩
  apply CategoryTheory.Functor.ext (fun _ ↦ Subsingleton.elim _ _)

/-- 概要：二点の thickening の Hom からの射は零単体上の値で決まる。
方針：入力単体が定値であることと定値単体の自然性を使う。
規約：任意の単体集合を標的にできる。
使われ方：Kerodon §2.4.3（Tag 00KM）、一単体の非対角 Hom の一意性。 -/
lemma coherentOneHom_map_constant {X : SSet.{u}} (i j : ULift.{u} (Fin 2))
    (f : nerve (SimplicialThickening.Path i j) ⟶ X) (n : ℕ)
    (P : (nerve (SimplicialThickening.Path i j)) _⦋n⦌) :
    f.app (Opposite.op ⦋n⦌) P =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (f.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ (P.obj 0))) n := by
  rw [coherentOneHom_simplex_constant i j n P]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map f _ n

/-- 概要：coherent nerve の一単体は抽出した通常の射から復元できる。
方針：対象を二頂点で比較し、対角 Hom は恒等、非対角 Hom は標準 path で比較する。
規約：豊穣 Hom に Kan 性を仮定しない。
使われ方：Kerodon Remark 3.1.6.3（Tag 01YZ）、pointed-space fiber の零単体の全射性。 -/
lemma coherentNerveArrowData_reconstruct {C : Type v} [Category.{u} C]
    [SimplicialCategory C] (s : (SimplicialNerve C) _⦋1⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C).app (Opposite.op ⦋1⦌)
      (ComposableArrows.mk₁ (coherentNerveArrowData s).2.2) = s := by
  apply EnrichedFunctor.ext SSet (fun i ↦ by
    rcases i with ⟨⟨i⟩⟩
    fin_cases i <;> rfl)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  fin_cases i <;> fin_cases j
  · simp only [eqToHom_refl, Category.comp_id]
    haveI := coherentOne_eId_epi (⟨ULift.up 0⟩ : SimplicialThickening (ULift.{u} (Fin 2)))
    apply (cancel_epi (eId SSet (⟨ULift.up 0⟩ :
      SimplicialThickening (ULift.{u} (Fin 2))))).1
    erw [EnrichedFunctor.map_id, s.map_id]
    rfl
  · simp only [eqToHom_refl, Category.comp_id]
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro P
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
      (SimplicialCategory.homEquiv' _ _ ((SimplicialCategory.homEquiv' _ _).symm
        ((s.map ⟨ULift.up 0⟩ ⟨ULift.up 1⟩).app (Opposite.op ⦋0⦌)
          (ComposableArrows.mk₀ coherentOnePath)))) n = _
    rw [Equiv.apply_symm_apply]
    erw [coherentOneHom_map_constant (ULift.up 0) (ULift.up 1)
      (s.map ⟨ULift.up 0⟩ ⟨ULift.up 1⟩) n P]
    have hp : P.obj 0 = coherentOnePath :=
      @Subsingleton.elim (SimplicialThickening.Path (ULift.up 0) (ULift.up 1))
        (coherentOnePath_subsingleton _ _) _ _
    rw [hp]
    rfl
  · simp only [eqToHom_refl, Category.comp_id]
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro P
    have h := SimplicialThickening.Path.le (P.obj 0)
    change (1 : Fin 2) ≤ 0 at h
    exact (by omega : False).elim
  · simp only [eqToHom_refl, Category.comp_id]
    haveI := coherentOne_eId_epi (⟨ULift.up 1⟩ : SimplicialThickening (ULift.{u} (Fin 2)))
    apply (cancel_epi (eId SSet (⟨ULift.up 1⟩ :
      SimplicialThickening (ULift.{u} (Fin 2))))).1
    erw [EnrichedFunctor.map_id, s.map_id]
    rfl

/-- 概要：coherent nerve の一単体と通常の射の端点付きデータは同値。
方針：抽出と通常の nerve からの標準射を互いに逆とする。
規約：右辺は対象二つとその間の射の依存和。
使われ方：Kerodon Remark 3.1.6.3（Tag 01YZ）、𝒮 の一単体を Kan 複体間の写像として読む。 -/
noncomputable def coherentNerveArrowDataEquiv (C : Type v) [Category.{u} C]
    [SimplicialCategory C] : (SimplicialNerve C) _⦋1⦌ ≃ (Σ X Y : C, X ⟶ Y) where
  toFun := coherentNerveArrowData
  invFun a := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ a.2.2)
  left_inv := coherentNerveArrowData_reconstruct
  right_inv a := coherentNerveArrowData_of_arrow a.2.2

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
