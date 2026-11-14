module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.PerfectModels
public import SerrePositivity.PerfectComplex.ClosedSupport
public import SerrePositivity.CategoryTheory.ScalarSupport

/-! # コホモロジーの台と完全モデル

概要：任意の閉集合に台を持つ複体の閉性と、完全モデル上のスカラー台条件との比較を与える。
方針：台条件を複体ホモトピー圏へ移し、完全モデルでは有限射影代表で既存の比較を使う。
規約：一般の台条件に恒等射の一様な冪消去を課さない。
使われ方：D_Z(S) と Perf_Z(S) の対象条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
open scoped ZeroObject
variable (S : Type u) [CommRing S]

/-- 概要：ホモトピー圏の対象の全ホモロジーが閉集合 Z に台を持つ条件。
方針：各次数のホモロジー関手の値の加群の台を使う。
規約：有界性・有限生成性は仮定しない。使われ方：台の閉性の転送。 -/
def supportHomotopyProperty (Z : TopologicalSpace.Closeds (PrimeSpectrum S)) :
    ObjectProperty (_root_.HomotopyCategory (ModuleCat.{u} S) (.up ℤ)) := fun X =>
  ∀ i : ℤ, Module.support S
    ((HomotopyCategory.homologyFunctor (ModuleCat S) (.up ℤ) i).obj X) ⊆ Z

/-- 概要：ホモトピー商の台条件は元の複体のコホモロジーの台条件である。
方針：ホモロジー比較同型の線形同値が台を保つことを使う。
規約：全整数次数。使われ方：複体レベルへの往復。 -/
lemma supportHomotopyProperty_quotient
    (Z : TopologicalSpace.Closeds (PrimeSpectrum S)) (P : Complex S) :
    supportHomotopyProperty S Z ((HomotopyCategory.quotient _ _).obj P) ↔
      HasHomologySupportOn Z P := by
  apply forall_congr'
  intro i
  exact (congrArg (fun A : Set (PrimeSpectrum S) => A ⊆ (Z : Set (PrimeSpectrum S)))
    (((HomotopyCategory.homologyFunctorFactors _ _ i).app P).toLinearEquiv.support_eq)).to_iff

/-- 概要：台条件はホモトピー圏での同型で保たれる。
方針：各次数でホモロジー同型を使う。
規約：一般の非有界複体を含む。使われ方：同型閉包との比較。 -/
instance supportHomotopyProperty_isoClosed
    (Z : TopologicalSpace.Closeds (PrimeSpectrum S)) :
    (supportHomotopyProperty S Z).IsClosedUnderIsomorphisms where
  of_iso e h i := by
    let ei := (HomotopyCategory.homologyFunctor (ModuleCat S) (.up ℤ) i).mapIso e
    rw [← ei.toLinearEquiv.support_eq]
    exact h i

/-- 概要：台を持つホモトピー型は零対象を含む。
方針：零複体の零ホモロジーを使う。
規約：空の閉集合も許す。使われ方：有限直和の閉性。 -/
instance supportHomotopyProperty_containsZero
    (Z : TopologicalSpace.Closeds (PrimeSpectrum S)) :
    (supportHomotopyProperty S Z).ContainsZero where
  exists_zero := ⟨(HomotopyCategory.quotient _ _).obj (0 : Complex S),
    (HomotopyCategory.quotient _ _).map_isZero (isZero_zero _),
    (supportHomotopyProperty_quotient S Z _).2 (hasHomologySupportOn_of_isZero (isZero_zero _))⟩

/-- 概要：台を持つホモトピー型は整数シフトで閉じる。
方針：複体の代表に戻し、既存のホモロジーシフト比較を使う。
規約：全整数シフト。使われ方：fiber の閉性。 -/
instance supportHomotopyProperty_shift
    (Z : TopologicalSpace.Closeds (PrimeSpectrum S)) :
    (supportHomotopyProperty S Z).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨by
    intro X hX
    obtain ⟨P, rfl⟩ := X.quotient_obj_surjective
    rw [ObjectProperty.prop_shift_iff, HomotopyCategory.shift_quotient_obj,
      supportHomotopyProperty_quotient]
    exact ((supportHomotopyProperty_quotient S Z P).1 hX).shift n⟩

/-- 概要：台を持つホモトピー型は distinguished triangle の第三項で閉じる。
方針：写像錐の長完全列による台の閉性を使う。
規約：完全性から出る台の評価のみを用いる。使われ方：三角閉性。 -/
instance supportHomotopyProperty_closed₃
    (Z : TopologicalSpace.Closeds (PrimeSpectrum S)) :
    (supportHomotopyProperty S Z).IsTriangulatedClosed₃ :=
  homotopyProperty_isTriangulatedClosed₃ _ _ (supportHomotopyProperty_quotient S Z)
    (fun f hP hQ => hP.mappingCone f hQ)

/-- 概要：台を持つホモトピー型は三角部分圏をなす。
方針：シフトと写像錐の閉性を組み合わせる。
規約：一般の閉集合。使われ方：有限直和の閉性。 -/
instance supportHomotopyProperty_triangulated
    (Z : TopologicalSpace.Closeds (PrimeSpectrum S)) :
    (supportHomotopyProperty S Z).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

/-- 概要：有限直和の全ホモロジーは、各項のホモロジーと同じ閉集合に台を持つ。
方針：加法的ホモトピー商が有限積を保存することを使う。
規約：任意の有限添字。使われ方：D_Z の有限直和閉性。 -/
lemma homologySupport_finiteBiproduct
    (Z : TopologicalSpace.Closeds (PrimeSpectrum S)) {I : Type v} [Finite I]
    (P : I → Complex S) (hP : ∀ i, HasHomologySupportOn Z (P i)) :
    HasHomologySupportOn Z (⨁ P) := by
  apply (supportHomotopyProperty_quotient S Z _).1
  exact (supportHomotopyProperty S Z).prop_of_isLimit
    (isLimitOfPreserves (HomotopyCategory.quotient _ _) (biproduct.isLimit P))
    (fun i => (supportHomotopyProperty_quotient S Z _).2 (hP i.as))

/-- 概要：二項直和のホモロジーは同じ閉集合に台を持つ。
方針：既存の二項直和のホモロジー比較を使う。
規約：追加の有界性なし。使われ方：標準 fiber の始域。 -/
lemma homologySupport_binaryBiproduct
    (Z : TopologicalSpace.Closeds (PrimeSpectrum S)) {P Q : Complex S}
    (hP : HasHomologySupportOn Z P) (hQ : HasHomologySupportOn Z Q) :
    HasHomologySupportOn Z (P ⊞ Q) := hP.biprod hQ

/-- 概要：台を持つ複体間の射の fiber も同じ台条件を持つ。
方針：写像錐と −1 シフトの閉性を合成する。
規約：D4 の標準 fiber。使われ方：D_Z の fiber 閉性。 -/
lemma homologySupport_fiber
    (Z : TopologicalSpace.Closeds (PrimeSpectrum S)) {P Q : Complex S} (f : P ⟶ Q)
    (hP : HasHomologySupportOn Z P) (hQ : HasHomologySupportOn Z Q) :
    HasHomologySupportOn Z ((CochainComplex.mappingCone f)⟦(-1 : ℤ)⟧) :=
  (hP.mappingCone f hQ).shift (-1)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
