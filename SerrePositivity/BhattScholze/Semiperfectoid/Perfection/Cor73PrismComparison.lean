module
public meta import SerrePositivity.Util.Citation

public import SerrePositivity.BhattScholze.Semiperfectoid.Perfection.InitialPrismPerfection
public import SerrePositivity.BhattScholze.Semiperfectoid.Perfection.Perfectoidization

/-!
# 初期 prism の完全化と Corollary 7.3

## 概要
同じ環の perfectoid 化を与える二つの完全 prism を、剰余単位を保つ唯一の同型で結ぶ。
## 方針
perfectoid 化の唯一の環同型を Lemma 4.8 で両方向へ持ち上げる。
## 規約
BS 著者版 Corollary 7.3・Proposition 7.10。候補は実 δ 除算・完全化・実完備化から作る。
## 使われ方
S′ 上の標準完全化と原典の Corollary 7.3 の候補の照合。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open _root_.SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime] {T B C : Type u} [CommRing T] [CommRing B] [CommRing C]

/-- 概要：同じ perfectoid 化を与える完全 prism には、単位を保つ唯一の δ-prism 同型がある。
方針：剰余の同型を両方向へ持ち上げ、剰余射の剛性で両逆を確認する。
規約：BS 著者版 Theorem 3.10・Corollary 7.3。零環も許す一般の比較。
使われ方：初期包絡の完全化と具体的な Corollary 7.3 候補。 -/
theorem existsUnique_perfectPrismComparison (Q : OrientedPrism p B)
    (hQ : Q.deltaStructure.IsPerfect) (v : T →+* B ⧸ Q.ideal) (hv : IsPerfectoidization p v)
    (V : OrientedPrism p C) (hV : V.deltaStructure.IsPerfect)
    (w : T →+* C ⧸ V.ideal) (hw : IsPerfectoidization p w) :
    ∃! F : OrientedPrism.Hom Q V, F.quotientMap.comp v = w ∧
      ∃ G : OrientedPrism.Hom V Q, G.comp F = OrientedPrism.Hom.id Q ∧ F.comp G = OrientedPrism.Hom.id V := by
  have hbQ : IsBoundedPrism Q := ⟨1, fun n x hx => by
    simpa only [pow_one] using Q.quotient_p_pow_torsion_killed_by_p hQ n x hx⟩
  have hbV : IsBoundedPrism V := ⟨1, fun n x hx => by
    simpa only [pow_one] using V.quotient_p_pow_torsion_killed_by_p hV n x hx⟩
  obtain ⟨e, he⟩ := IsPerfectoidization.exists_equiv p hv hw
  obtain ⟨F, hF, _⟩ := _root_.SerrePositivity.BhattScholze.existsUnique_perfectPrismHomLift_to_bounded Q hQ V hbV e.toRingHom
  obtain ⟨G, hG, _⟩ := _root_.SerrePositivity.BhattScholze.existsUnique_perfectPrismHomLift_to_bounded V hV Q hbQ e.symm.toRingHom
  have hGF : G.comp F = OrientedPrism.Hom.id Q := by
    apply _root_.SerrePositivity.BhattScholze.perfectPrismHom_ext_to_bounded_target Q hQ Q hbQ
    rw [OrientedPrism.Hom.quotientMap_comp, hG, hF, OrientedPrism.Hom.quotientMap_id]
    apply RingHom.ext
    intro x
    exact e.symm_apply_apply x
  have hFG : F.comp G = OrientedPrism.Hom.id V := by
    apply _root_.SerrePositivity.BhattScholze.perfectPrismHom_ext_to_bounded_target V hV V hbV
    rw [OrientedPrism.Hom.quotientMap_comp, hG, hF, OrientedPrism.Hom.quotientMap_id]
    apply RingHom.ext
    intro x
    exact e.apply_symm_apply x
  refine ⟨F, ⟨by rw [hF]; exact he, G, hGF, hFG⟩, ?_⟩
  intro k hk
  apply _root_.SerrePositivity.BhattScholze.perfectPrismHom_ext_to_bounded_target Q hQ V hbV
  exact ((hv.2 (C ⧸ V.ideal) hw.1 w).unique hk.1 he).trans hF.symm

variable {A : Type u} [CommRing A]

/-- Corollary 7.3 の具体的候補への、単位を保つ唯一の δ-prism 同型。 -/
def IsClassicalCor73Comparison (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)
    (r : A →+* T) (hr : Function.Surjective r) (Q : OrientedPrism p B) (v : T →+* B ⧸ Q.ideal) : Prop :=
  letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismCommRing P.deltaStructure P.generator (RingHom.ker r)
  let V := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrism P.deltaStructure P.generator P.isDistinguished_generator (RingHom.ker r)
  let w := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectPrismQuotientPerfectoidizationMap P hP r hr
  ∃! F : OrientedPrism.Hom Q V, F.quotientMap.comp v = w ∧
    ∃ G : OrientedPrism.Hom V Q, G.comp F = OrientedPrism.Hom.id Q ∧ F.comp G = OrientedPrism.Hom.id V

/-- 概要：初期 prism の標準完全化は、同じ全射商の Corollary 7.3 の候補と一意に同型。
方針：初期性からの perfectoid 化と、Corollary 7.3 の具体的 perfectoid 化を比較する。
規約：BS 著者版 Proposition 7.10・Corollary 7.3。非零の枝の原典の入口を明示する。
使われ方：S′ 単位を保つ完全化との一致。 -/
theorem classicalPrismPerfection_cor73 (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)
    [Fact (¬ IsUnit (p : A ⧸ P.ideal))] (r : A →+* T) (hr : Function.Surjective r)
    (hrd : r P.generator = 0) (Q : OrientedPrism p B) (v : T →+* B ⧸ Q.ideal)
    (hv : IsInitialPrismUnit Q v) :
    IsClassicalCor73Comparison P hP r hr (classicalPrismPerfection Q) (classicalPrismPerfectionUnit Q v) := by
  letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismCommRing P.deltaStructure P.generator (RingHom.ker r)
  exact existsUnique_perfectPrismComparison (classicalPrismPerfection Q)
    (classicalPrismPerfection_isPerfect Q) (classicalPrismPerfectionUnit Q v)
    (classicalPrismPerfectionUnit_isPerfectoidization Q v hv)
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrism P.deltaStructure P.generator P.isDistinguished_generator (RingHom.ker r))
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrism_isPerfect P.deltaStructure P.generator P.isDistinguished_generator (RingHom.ker r))
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectPrismQuotientPerfectoidizationMap P hP r hr)
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectPrismQuotientPerfectoidizationMap_isPerfectoidization P hP r hr hrd)

/-- 概要：零環の商の枝でも、完全化と Corollary 7.3 の候補は単位を保って一意に同型。
方針：零環から射を受ける剰余と標的は零環なので、perfectoid 化の普遍性は自明。
規約：BS 著者版 Proposition 7.10・Corollary 7.3 の退化した枝。
使われ方：S′ の根付き基底が零環の場合を非零性仮定なしで閉じる。 -/
theorem classicalPrismPerfection_cor73_of_subsingleton [Subsingleton T]
    (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)
    (r : A →+* T) (hr : Function.Surjective r)
    (Q : OrientedPrism p B) (v : T →+* B ⧸ Q.ideal) (hv : IsInitialPrismUnit Q v) :
    IsClassicalCor73Comparison P hP r hr
      (classicalPrismPerfection Q) (classicalPrismPerfectionUnit Q v) := by
  letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismCommRing P.deltaStructure P.generator (RingHom.ker r)
  let V := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrism P.deltaStructure P.generator
    P.isDistinguished_generator (RingHom.ker r)
  let w := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectPrismQuotientPerfectoidizationMap P hP r hr
  have hw : IsPerfectoidization p w := by
    letI := w.codomain_trivial
    refine ⟨Or.inl inferInstance, ?_⟩
    intro D _ _ s
    letI : Subsingleton D := s.codomain_trivial
    let l : _root_.SerrePositivity.BhattScholze.Semiperfectoid.PerfectDeltaDivisionPrismCarrier P.deltaStructure P.generator (RingHom.ker r) ⧸
        V.ideal →+* D := {
      toFun := fun _ => 0
      map_one' := Subsingleton.elim _ _
      map_mul' := fun _ _ => Subsingleton.elim _ _
      map_zero' := rfl
      map_add' := fun _ _ => Subsingleton.elim _ _ }
    exact ⟨l, RingHom.ext (fun _ => Subsingleton.elim _ _),
      fun _ _ => RingHom.ext (fun _ => Subsingleton.elim _ _)⟩
  exact existsUnique_perfectPrismComparison _ (classicalPrismPerfection_isPerfect Q) _
    (classicalPrismPerfectionUnit_isPerfectoidization Q v hv) V
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrism_isPerfect _ _ _ _) w hw

end SerrePositivity.BhattScholze.Semiperfectoid

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Prop 7.10" (partial := component) "BS-W17 H5（11-12）：T（有限）と S′（任意添字）の古典的な部分は本体：固定 A_inf 上の有界な実包絡、全有界 prism への一意な射、S′ の完全化と Cor 7.3 の単位を保つ唯一の同型（停止点 4・5a・5）。S′ の単位の完全忠実平坦性は後回し（E3 は使わない）。Δ_R/A との同定（G10）は drafts ／ 11-12 節の見直し：S′ の部分は f_j=0 の場合（根の商）だけ"] _root_.SerrePositivity.BhattScholze.Semiperfectoid.classicalPrismPerfection_cor73
attribute [cite BS19 "Prop 7.10" (partial := component) "BS-W17 H5（11-12）：T（有限）と S′（任意添字）の古典的な部分は本体：固定 A_inf 上の有界な実包絡、全有界 prism への一意な射、S′ の完全化と Cor 7.3 の単位を保つ唯一の同型（停止点 4・5a・5）。S′ の単位の完全忠実平坦性は後回し（E3 は使わない）。Δ_R/A との同定（G10）は drafts ／ 11-12 節の見直し：S′ の部分は f_j=0 の場合（根の商）だけ"] _root_.SerrePositivity.BhattScholze.Semiperfectoid.existsUnique_perfectPrismComparison
