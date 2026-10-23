module

public import SerrePositivity.InfinityCategories.F1.IntervalCosliceRigidity
public import SerrePositivity.InfinityCategories.F1.Cocartesian.SourceRestriction

/-!
概要：区間上の cocartesian な辺を固定した三角形の始点側の比較。
方針：基底の錐の一意性で相対 coslice のデータを補い、cocartesian 性による充填を終点 fiber に戻す。
規約：辺は標準区間を被覆し、固定終点は時刻一にある。
使われ方：Kerodon Proposition 5.1.3.11、Proposition 5.1.6.7、transport による前向きの写像空間の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：標準単体内の図式の錐はその終点から一意に決まる。
方針：固定した左図式と右因子の一致により各次数の錐を検出する。
規約：図式の形は任意。
使われ方：Kerodon Proposition 5.1.3.11、基底側の可換条件の検査。 -/
instance sliceUnderProjection_stdSimplex_mono {K : SSet.{u}} {n : ℕ}
    (e : K ⟶ (Δ[n] : SSet.{u})) : Mono (sliceUnderProjection e) := by
  have happ : ∀ d, Mono ((sliceUnderProjection e).app d) := by
    intro d
    apply (mono_iff_injective _).mpr
    intro s t h
    apply Subtype.ext
    apply join_hom_ext_stdSimplex_factors
    · exact s.property.trans t.property.symm
    · apply SSet.yonedaEquiv.injective
      exact h
  exact NatTrans.mono_of_mono_app _

/-- 概要：coslice の後合成は錐の可変部分への射影を保つ。
方針：右包含の後の Yoneda の評価と後合成の自然性を使う。
規約：図式と後合成する射は任意。
使われ方：Kerodon Proposition 5.1.3.11、三角形の基底と終点の整合性。 -/
lemma sliceUnderPostcomp_projection {K X Y : SSet.{u}} (e : K ⟶ X) (p : X ⟶ Y) :
    sliceUnderPostcomp e p ≫ sliceUnderProjection (e ≫ p) = sliceUnderProjection e ≫ p := rfl

/-- 概要：区間を被覆する cocartesian 辺を固定した三角形の始点への制限は trivial Kan fibration。
方針：標準的な基底の錐を相対制限の標的に加え、その充填を終点固定の fiber に戻す。
規約：全空間の quasicategory 性は不要、終点の時刻は一。
使われ方：Kerodon Proposition 5.1.3.11、Proposition 5.1.6.7、transport による写像空間の比較。 -/
lemma cosliceTriangleSource_trivialKanFibration {E : SSet.{u}}
    (p : E ⟶ (Δ[1] : SSet.{u})) (e : (Δ[1] : SSet.{u}) ⟶ E)
    (hp : e ≫ p = 𝟙 Δ[1]) (he : IsCocartesianEdge p (SSet.yonedaEquiv e))
    (y : E _⦋0⦌) (hy : p.app (Opposite.op ⦋0⦌) y = stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :
    TrivialKanFibration (cosliceRestrictionFiberMap e (stdSimplex.δ (1 : Fin 2)) y) := by
  let i : (Δ[0] : SSet.{u}) ⟶ Δ[1] := stdSimplex.δ 1
  let r := relativeCosliceRestriction e p i
  have hr : TrivialKanFibration r := relativeCosliceRestriction_source_of_isCocartesianEdge e p he
  let v : (sliceUnder (e ≫ p)) _⦋0⦌ :=
    ⟨intervalIdentityCosliceVertex.val, intervalIdentityCosliceVertex.property.trans hp.symm⟩
  have hv : (sliceUnderProjection (e ≫ p)).app (Opposite.op ⦋0⦌) v =
      stdSimplex.obj₀Equiv.symm (1 : Fin 2) := by
    exact congrArg (fun h ↦ h.app (Opposite.op ⦋0⦌) intervalIdentityCosliceVertex)
      intervalIdentityCoslice_projection
  have hsub (m : ℕ) : Subsingleton ((sliceUnder (e ≫ p)) _⦋m⦌) := by
    rw [hp]
    infer_instance
  apply (trivialKanFibration_iff_boundary _).mpr
  intro n
  have := hr.mem (boundary n).ι inferInstance
  constructor
  intro a b sq
  let a0 := a ≫ vertexFiberι (sliceUnderProjection e) y
  let b0 := b ≫ vertexFiberι (sliceUnderProjection (i ≫ e)) y
  have hw : b0 ≫ sliceUnderPostcomp (i ≫ e) p =
      (SSet.const v : (Δ[n] : SSet.{u}) ⟶ sliceUnder (e ≫ p)) ≫
        sliceUnderRestrict (e ≫ p) i := by
    apply (cancel_mono (sliceUnderProjection ((i ≫ e) ≫ p))).mp
    rw [Category.assoc, sliceUnderPostcomp_projection]
    rw [← Category.assoc, show b0 ≫ sliceUnderProjection (i ≫ e) = SSet.const y from
      by simp only [b0, Category.assoc, vertexFiberι_comp, SSet.comp_const]]
    rw [SSet.const_comp, hy]
    have hproj : sliceUnderRestrict (e ≫ p) i ≫ sliceUnderProjection ((i ≫ e) ≫ p) =
        sliceUnderProjection (e ≫ p) := sliceUnderRestrict_projection (e ≫ p) i
    rw [Category.assoc, hproj, SSet.const_comp, hv]
  let d := pullback.lift b0 (SSet.const v) hw
  have ha : a0 ≫ sliceUnderRestrict e i = (boundary n).ι ≫ b0 := by
    have hh := congrArg (fun t ↦ t ≫ vertexFiberι (sliceUnderProjection (i ≫ e)) y) sq.w
    exact hh
  have hd : a0 ≫ r = (boundary n).ι ≫ d := by
    apply pullback.hom_ext
    · simpa only [r, relativeCosliceRestriction, squareComparison, Category.assoc,
        pullback.lift_fst, d] using ha
    · apply SSet.hom_ext
      rintro ⟨⟨m⟩⟩
      apply ConcreteCategory.hom_ext
      intro z
      exact (hsub m).elim _ _
  let t : CommSq a0 (boundary n).ι r d := ⟨hd⟩
  have hb : t.lift ≫ sliceUnderRestrict e i = b0 := by
    have hh := congrArg (fun h ↦ h ≫ pullback.fst (sliceUnderPostcomp (i ≫ e) p)
      (sliceUnderRestrict (e ≫ p) i)) t.fac_right
    simpa only [r, relativeCosliceRestriction, squareComparison, d, Category.assoc,
      pullback.lift_fst] using hh
  have ht : t.lift ≫ sliceUnderProjection e = SSet.const y := by
    calc
      _ = t.lift ≫ (sliceUnderRestrict e i ≫ sliceUnderProjection (i ≫ e)) :=
        congrArg (fun h ↦ t.lift ≫ h) (sliceUnderRestrict_projection e i).symm
      _ = (t.lift ≫ sliceUnderRestrict e i) ≫ sliceUnderProjection (i ≫ e) :=
        (Category.assoc _ _ _).symm
      _ = _ := by
        rw [hb]
        simp only [b0, Category.assoc, vertexFiberι_comp, SSet.comp_const]
  refine CommSq.HasLift.mk' {
    l := vertexFiberLift (sliceUnderProjection e) y t.lift ht
    fac_left := ?_
    fac_right := ?_ }
  · apply vertexFiber_hom_ext
    rw [Category.assoc, vertexFiberLift_ι]
    exact t.fac_left
  · apply vertexFiber_hom_ext
    exact hb

end SerrePositivity.InfinityCategories
