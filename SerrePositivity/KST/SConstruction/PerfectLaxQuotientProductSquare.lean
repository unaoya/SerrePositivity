module
public import SerrePositivity.KST.SConstruction.PerfectLaxQuotientValueVertices
public import SerrePositivity.KST.SConstruction.TammePerfectProjectionEquivalence
public import SerrePositivity.KST.LocalizingInvariants.DiagramVertexTransport

/-! # 元の C・D の値の実 BF 積への全比較正方形の移送
概要：Tamme の元の両射影同値を四角に指定し、全図式の同型と引き戻し性を保つ。
方針：頂点同型の可逆 path 全族を延長し、同じ実 Sp 正方形を移す。
規約：四辺の類だけで正方形を選び直さない。使われ方：元の商の二脚の切除。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories LocalizingInvariants
open scoped Simplicial
namespace PerfectLaxQuotient
local instance productSquareSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
variable {C D B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D B}
  (d : PerfectLaxQuotient p q)
  {F : perfectStableInfinity.{u} ⟶ Sp.{u}} (hF : IsPerfectLocalizingInvariant F)

/-- 元の値と二つの元の実 BF 積に向かう、同じ四頂点の指定同型。 -/
def productCornerIso (a b : Fin 2) : Σ x : Sp.{u} _⦋0⦌,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (d.universalValueSquare F) a b) x := by
  refine Fin.cases ?_ (fun a => ?_) a
  · refine Fin.cases ?_ (fun b => ?_) b
    · exact ⟨_, eqToIso (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj Sp.{u}))
        (d.universalValueSquare_vertex00 F)) ≪≫
          (perfectInvariantSpectrumIso F (perfectStableVertex d.left d.left_complete)).symm⟩
    · have hb : b = 0 := by apply Fin.ext; omega
      subst b
      exact ⟨_, eqToIso (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj Sp.{u}))
        (d.universalValueSquare_vertex01 F)) ≪≫
          (perfectInvariantSpectrumIso F d.sequence.rightVertex).symm⟩
  · have ha : a = 0 := by apply Fin.ext; omega
    subst a
    refine Fin.cases ?_ (fun b => ?_) b
    · exact ⟨_, eqToIso (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj Sp.{u}))
        (d.universalValueSquare_vertex10 F)) ≪≫
          (perfectInvariantSpectrumIso F (perfectLaxVertex p q d.c_complete d.d_complete)).symm ≪≫
            hF.tammePerfectProjectionEquivalence p q d.c_complete d.d_complete⟩
    · have hb : b = 0 := by apply Fin.ext; omega
      subst b
      exact ⟨_, eqToIso (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj Sp.{u}))
        (d.universalValueSquare_vertex11 F)) ≪≫
          (perfectInvariantSpectrumIso F
            (perfectLaxVertex (𝟙 d.sequence.right) (𝟙 d.sequence.right)
              d.sequence.right_complete d.sequence.right_complete)).symm ≪≫
            hF.tammePerfectProjectionEquivalence (𝟙 d.sequence.right) (𝟙 d.sequence.right)
              d.sequence.right_complete d.sequence.right_complete⟩

/-- 元の全正方形の任意の頂点に、指定した同じ移送先と同型を与える。 -/
def productVertexIsos (v : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) _⦋0⦌) : Σ x : Sp.{u} _⦋0⦌,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((d.universalValueSquare F).app (Opposite.op ⦋0⦌) v) x := by
  let a := stdSimplex.obj₀Equiv v.1
  let b := stdSimplex.obj₀Equiv v.2
  have he : (d.universalValueSquare F).app (Opposite.op ⦋0⦌) v =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (d.universalValueSquare F) a b := by
    change _ = (d.universalValueSquare F).app _
      (stdSimplex.obj₀Equiv.symm (stdSimplex.obj₀Equiv v.1),
        stdSimplex.obj₀Equiv.symm (stdSimplex.obj₀Equiv v.2))
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rfl
  exact ⟨(d.productCornerIso hF a b).1,
    eqToIso (congrArg HomotopyCategory.mk he) ≪≫ (d.productCornerIso hF a b).2⟩

/-- 同じ指定四頂点の可逆 path 全族。 -/
def productVertexPaths : DiagramVertexPaths (d.universalValueSquare F) :=
  DiagramVertexPaths.ofIso (d.productVertexIsos hF)

/-- 同じ可逆 path 全族の、全図式への実延長。 -/
def productExtension : (d.productVertexPaths hF).Extension := (d.productVertexPaths hF).extension

/-- 元の C・D の値と完備化先の値の実積を四角に持つ、移送した全正方形。 -/
def productSquare : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u} := (d.productExtension hF).target

/-- 元の比較正方形と同じ全単体上で整合する、実関手同型。 -/
def productComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d.universalValueSquare F) (d.productSquare hF) :=
  (d.productExtension hF).comparison

/-- 元の全図式の同型で移した同じ実積正方形は、実 Sp の引き戻し。 -/
lemma productSquare_isPullback : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (d.productSquare hF) :=
  (d.productExtension hF).target_isPullback (d.universalValueSquare_isPullback hF)

end PerfectLaxQuotient
end SerrePositivity.KST.SConstruction
