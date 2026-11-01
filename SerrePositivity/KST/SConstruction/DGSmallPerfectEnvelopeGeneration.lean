module
public import SerrePositivity.KST.SConstruction.DGSmallPerfectEnvelopeEquivalence
public import SerrePositivity.KST.SConstruction.DGGeneratorImagePerfect
public import SerrePositivity.DifferentialGraded.Morita.QuasiEquivalenceGraph

/-! # 元の小代表の生成条件を実延長像を含む小模型へ送る
概要：元の小代表系の指定生成条件を、同じ実対象を含む拡張模型へ移す。
方針：同じ準同値包含の既存導来順逆と代表比較を使い、実自由代表へ H⁰ 同型で移す。
規約：元の小代表の生成条件は明示入力。使われ方：D が供給する実 LT 入力の接続。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (J : Type w) [Small.{u} J] (X : J → PerfectDGModule R D)
local notation "S" => SmallPerfectDGModuleOver R D Set.univ
local notation "C" => DGSmallPerfectEnvelope R D J X
local notation "F" => dgSmallPerfectEnvelopeSmallInclusion R D J X
local instance : (dgDerivedExtension R (S) (C) (F)).CommShift ℤ :=
  dgDerivedExtensionCommShift R (S) (C) (F)
local instance : (dgDerivedExtension R (S) (C) (F)).IsTriangulated :=
  dgDerivedExtensionIsTriangulated R (S) (C) (F)

/-- 元の小代表の単一生成は、同じ実対象を含む拡張模型にも移る。 -/
lemma dgSmallPerfectEnvelope_perfectOver_smallPoint_eq (b : S)
    (hgen : modulePerfectOver R (S) {b} = modulePerfect R (S)) :
    modulePerfectOver R (C) {dgSmallPerfectEnvelopeOfSmall R D J X b} =
      modulePerfect R (C) := by
  let P := modulePerfectOver R (C) {dgSmallPerfectEnvelopeOfSmall R D J X b}
  let H := P.inverseImage (dgDerivedExtension R (S) (C) (F))
  have : H.IsTriangulated := by dsimp [H]; infer_instance
  have : H.IsClosedUnderIsomorphisms := by dsimp [H]; infer_instance
  have : H.IsStableUnderRetracts :=
    ⟨fun r hy => P.prop_of_retract (r.map (dgDerivedExtension R (S) (C) (F))) hy⟩
  have hs : modulePerfectOver R (S) {b} ≤ H := by
    apply modulePerfectOver_le_of_generators R (S) H
    intro y hy
    have hy : y = b := Set.mem_singleton_iff.mp hy
    subst y
    exact P.prop_of_iso (dgDerivedExtensionRepresentableIso R (S) (C) (F) b).symm
      (modulePerfectOver_representable R (C) _ (Set.mem_singleton _))
  have hall : modulePerfect R (S) ≤ H := hgen ▸ hs
  apply le_antisymm (modulePerfectOver_mono R (C) (Set.subset_univ _))
  intro Y hY
  let hF := dgSmallPerfectEnvelopeSmallInclusion_quasiEquivalence R D J X
  exact P.prop_of_iso ((dgFunctorDerivedEquivalence R (S) (C) (F) hF).counitIso.app Y)
    (hall _ (quasiEquivalenceRestriction_perfect R (S) (C) (F) hF hY))

/-- 元の小代表の生成と自由代表への H⁰ 比較から、模型内の実自由代表が生成する。 -/
lemma dgSmallPerfectEnvelope_perfectOver_representable_eq (b : S) (d : D)
    (hgen : modulePerfectOver R (S) {b} = modulePerfect R (S))
    (e : (smallPerfectDGModuleInclusion R D Set.univ).onHomotopy.obj
        ((toHomotopy R (S)).obj (ForgetEnrichment.of (Complex R) b)) ≅
      (toHomotopy R (PerfectDGModule R D)).obj
        (ForgetEnrichment.of (Complex R) (dgRepresentablePerfectPoint R D d))) :
    modulePerfectOver R (C) {dgSmallPerfectEnvelopeRepresentable R D J X d} =
      modulePerfect R (C) := by
  let I := dgSmallPerfectEnvelopeInclusion R D J X
  let hI : ∀ x y, IsIso (I.map x y) := by
    intro x y
    change IsIso (𝟙 _)
    infer_instance
  let : I.onHomotopy.Full := I.onHomotopy_full_of_homIso hI
  let : I.onHomotopy.Faithful := I.onHomotopy_faithful_of_homIso hI
  let eb : (toHomotopy R (C)).obj
      (ForgetEnrichment.of (Complex R) (dgSmallPerfectEnvelopeOfSmall R D J X b)) ≅
      (toHomotopy R (C)).obj
        (ForgetEnrichment.of (Complex R) (dgSmallPerfectEnvelopeRepresentable R D J X d)) :=
    I.onHomotopy.preimageIso e
  exact dgPerfectOver_singleton_eq_of_generator_iso R (C)
    (dgSmallPerfectEnvelopeOfSmall R D J X b)
    (dgSmallPerfectEnvelopeRepresentable R D J X d)
    (dgSmallPerfectEnvelope_perfectOver_smallPoint_eq R D J X b hgen)
    eb.symm

end SerrePositivity.KST.SConstruction
