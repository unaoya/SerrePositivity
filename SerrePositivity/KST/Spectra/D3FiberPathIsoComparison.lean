module

public import SerrePositivity.KST.Spectra.D3EquivalencePathIsoValues
public import SerrePositivity.InfinityCategories.F2.CatInfinity.EquivalenceHomotopyIsoPresentation

/-!
概要：定値 path との元の fiber 比較が、同じ指定 path の同型を回収することを認証する。
方針：普遍 path の自然性正方形と、始点評価の指定恒等値・定値族の恒等値を使う。
規約：fiber 内の比較を選び直さない。使われ方：既存 componentIso の指定値の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra

/-- 上辺と右辺が指定恒等である同じ正方形では、下辺の逆は左辺そのもの。 -/
lemma d3FunctorIso_standard_square_inv {A Y : SSet.{u}}
    {f0 f1 g0 g1 : A ⟶ Y} (a : FunctorIso f0 f1) (b : FunctorIso f1 g1)
    (c : FunctorIso f0 g0) (d : FunctorIso g0 g1)
    (ha : F2.IsFunctorEqIso a) (hb : F2.IsFunctorEqIso b) (h : a ≪≫ b = c ≪≫ d) :
    HEq d.symm c := by
  obtain ⟨haf, ha⟩ := ha
  subst f1
  obtain ⟨hbg, hb⟩ := hb
  subst g1
  change a = Iso.refl _ at ha
  change b = Iso.refl _ at hb
  subst a b
  simp only [Iso.refl_trans] at h
  have hh := congrArg (fun z ↦ z ≪≫ d.symm) h
  exact heq_of_eq (by simpa only [Iso.refl_trans, Iso.trans_assoc,
    Iso.self_symm_id, Iso.trans_refl] using hh)

/-- 元の定値 path との fiber 比較を終点で逆向きに写すと、同じ path 同型を回収する。 -/
lemma d3TrivialPathFiberIso_value {A Y : SSet.{u}} [Quasicategory Y]
    (L : A ⟶ equivalencePath Y) (f : A ⟶ Y)
    (h : L ≫ equivalencePathEndpoint Y 0 =
      (f ≫ equivalencePathRefl Y) ≫ equivalencePathEndpoint Y 0) :
    HEq (FunctorIso.postcomp (functorIsoOfTrivialKanFibration (equivalencePathEndpoint Y 0)
      L (f ≫ equivalencePathRefl Y) h).symm (equivalencePathEndpoint Y 1))
      (equivalencePathFamilyIso L) := by
  let e := functorIsoOfTrivialKanFibration (equivalencePathEndpoint Y 0)
    L (f ≫ equivalencePathRefl Y) h
  have he : F2.IsFunctorEqIso (e.postcomp (equivalencePathEndpoint Y 0)) :=
    d3IsFunctorEqIso_of_eqToIso _ h
      (functorIsoOfTrivialKanFibration_postcomp _ _ _ h)
  have hs := F2.functorIso_whisker_exchange e (d3UniversalEquivalencePathIso Y)
  have hv := d3FunctorIso_standard_square_inv _ _ _ _ he
    (d3UniversalEquivalencePathIso_refl f) hs
  rw [F2.functorIso_postcomp_symm]
  exact hv.trans (heq_of_eq (d3UniversalEquivalencePathIso_precomp L))

/-- 元の可逆ホモトピーからの同型は、構成中の同じ path 族の指定同型に一致。 -/
lemma d3EquivalenceHomotopyIso_value {A Y : SSet.{u}} [Quasicategory Y]
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ Y)
    (hH : ∀ x : A _⦋0⦌, IsInvertibleEdge (edgeOfSimplex
      (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1)))) :
    HEq (functorIsoOfEquivalenceHomotopy H hH)
      (equivalencePathFamilyIso (F2.equivalenceHomotopyPathLift H hH)) := by
  refine (F2.functorIsoOfEquivalenceHomotopy_heq H hH).trans ?_
  exact d3TrivialPathFiberIso_value (F2.equivalenceHomotopyPathLift H hH)
    (prismEndpoint 0 A ≫ H) (by rw [F2.equivalenceHomotopyPathLift_endpoint,
      Category.assoc, equivalencePathRefl_endpoint, Category.comp_id])

end SerrePositivity.KST.Spectra
