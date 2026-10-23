module

public import SerrePositivity.InfinityCategories.F1B.RightAnodyneTensor
public import SerrePositivity.InfinityCategories.F1.Scaffold.ScaffoldFirstVertex
public import SerrePositivity.InfinityCategories.F1B.KanTerminalPointAnodyne
public import SerrePositivity.InfinityCategories.F2.Ind.ConeApexTerminal

/-!
概要：right fibration で、指定始点と right anodyne な側面を同時に保つ円柱持ち上げ。
方針：二つの境界を pushout-product に貼り、その right anodyne 性で持ち上げる。
規約：底の全円柱を厳密に回収。使われ方：射図式の終点 comma の円柱族の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 任意の試験形状の右余錐の頂点包含は right anodyne。 -/
lemma conePoint_rightAnodyne (A : SSet.{u}) :
    rightAnodyneExtensions (joinInr A (Δ[0] : SSet.{u})) := by
  have h := F1B.kanTerminalPoint_rightAnodyne (coneApex_isTerminalVertex A)
  have he : SSet.yonedaEquiv.symm (coneApex A) = joinInr A (Δ[0] : SSet.{u}) := by
    apply SSet.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    have hp : (stdSimplex.obj₀Equiv.symm 0 : (Δ[0] : SSet.{u}) _⦋0⦌) =
        SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
      apply stdSimplex.ext
      intro i
      apply Fin.ext
      omega
    exact congrArg (fun x => (joinInr A (Δ[0] : SSet.{u})).app (Opposite.op ⦋0⦌) x) hp
  rwa [he] at h

/-- 指定始点・指定側面を持つ元の全円柱を、right fibration へ持ち上げる。 -/
lemma exists_rightFibration_prism_corner_lift {A D E B : SSet.{u}}
    (p : E ⟶ B) [RightFibration p] (j : D ⟶ A) (hj : rightAnodyneExtensions j)
    (b : A ⊗ (Δ[1] : SSet.{u}) ⟶ B)
    (a : A ⊗ (Δ[0] : SSet.{u}) ⟶ E) (d : D ⊗ (Δ[1] : SSet.{u}) ⟶ E)
    (h : (j ▷ (Δ[0] : SSet.{u})) ≫ a = (D ◁ scaffoldFirstVertex 1) ≫ d)
    (ha : a ≫ p = (A ◁ scaffoldFirstVertex 1) ≫ b)
    (hd : d ≫ p = (j ▷ (Δ[1] : SSet.{u})) ≫ b) :
    ∃ W : A ⊗ (Δ[1] : SSet.{u}) ⟶ E,
      W ≫ p = b ∧ (A ◁ scaffoldFirstVertex 1) ≫ W = a ∧
        (j ▷ (Δ[1] : SSet.{u})) ≫ W = d := by
  let sq := CategoryTheory.Functor.PushoutObjObj.ofHasPushout
    (curriedTensor SSet.{u}) j (scaffoldFirstVertex 1)
  have hl : sq.inl ≫ sq.ι = A ◁ scaffoldFirstVertex 1 := sq.inl_ι
  have hr : sq.inr ≫ sq.ι = j ▷ (Δ[1] : SSet.{u}) := sq.inr_ι
  let t := sq.isPushout.desc a d h
  have ht : t ≫ p = sq.ι ≫ b := by
    apply sq.hom_ext
    · rw [← Category.assoc, sq.isPushout.inl_desc, ha,
        ← hl, Category.assoc]
    · rw [← Category.assoc, sq.isPushout.inr_desc, hd,
        ← hr, Category.assoc]
  have : HasLiftingProperty sq.ι p :=
    cofinalRightAnodyne_pushoutObjObj_left j hj (scaffoldFirstVertex 1) sq p
      (RightFibration.mem (p := p))
  let L : CommSq t sq.ι p b := ⟨ht⟩
  refine ⟨L.lift, L.fac_right, ?_, ?_⟩
  · rw [← hl, Category.assoc, L.fac_left, sq.isPushout.inl_desc]
  · rw [← hr, Category.assoc, L.fac_left, sq.isPushout.inr_desc]

end SerrePositivity.InfinityCategories.F2.Ind
