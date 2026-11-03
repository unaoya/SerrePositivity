module

public import SerrePositivity.KST.DerivedGeometry.LinearYonedaFunctor
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
public import SerrePositivity.DifferentialGraded.Perfect.RepresentableHomology
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
概要：複体の代表 dg 加群が有限 cell の操作で閉じることを証明する。
方針：射の持上げと具体的な shift・cone 同型を用いて操作木を帰納する。
規約：同型は実際の dg 加群圏で構成し、存在を仮定として入力しない。
使われ方：Drinfeld §2.4、KST D4・§10-7 の前三角化と H⁰ の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open scoped ZeroObject
namespace SerrePositivity.KST.DerivedGeometry.LinearComplex
variable (A : Type u) [CommRing A] {C : Type v} [Category.{u} C] [Preadditive C] [Linear A C]
attribute [local instance] enrichment
variable [Small.{u} (CochainComplex C ℤ)]

/--
概要：代表加群への具体的な関手は加法的。
方針：各評価の後合成が chain map の和を保つことを確認する。
規約：対象ごとの等式から加群射の等式を得る。
使われ方：Drinfeld §2.4、KST D4 の零・有限和の代表可能性。
-/
instance complexYoneda_additive : (complexYoneda (C := C) A).Additive where
  map_add {X Y} f g := by
    apply moduleMorphism_ext
    intro T
    rw [(moduleEvaluation A (CochainComplex C ℤ) T).map_add]
    change (moduleEvaluation A (CochainComplex C ℤ) T).map
      (representablePostcompose A (f + g)) =
      (moduleEvaluation A (CochainComplex C ℤ) T).map (representablePostcompose A f) +
      (moduleEvaluation A (CochainComplex C ℤ) T).map (representablePostcompose A g)
    rw [representablePostcompose_eval, representablePostcompose_eval,
      representablePostcompose_eval]
    ext q h
    change h.comp (Cochain.ofHom (f + g)) (add_zero q) =
      h.comp (Cochain.ofHom f) (add_zero q) + h.comp (Cochain.ofHom g) (add_zero q)
    rw [Cochain.ofHom_add, Cochain.comp_add]

variable [HasZeroObject C] [HasBinaryBiproducts C]

set_option maxHeartbeats 1000000 in
-- 全次数の cone と arrow の同型を含む帰納で、通常より多くの定義比較を行う。
set_option synthInstance.maxHeartbeats 100000 in
/--
概要：有限 cell の各構成結果は元の複体の代表加群で表現される。
方針：操作木の各段階で零・和・shift・cone の具体的な加群同型を構成する。
規約：cone の射は充満性で実際の chain map へ持ち上げる。
使われ方：Drinfeld §2.4、KST D4・§10-7 の前三角化の代表可能性。
-/
theorem finiteCell_representable {M : ModuleCategory A (CochainComplex C ℤ)}
    (c : ModuleFiniteCellCode A (CochainComplex C ℤ) Set.univ M) :
    ∃ X : CochainComplex C ℤ, Nonempty (M ≅ (complexYoneda A).obj X) := by
  induction c with
  | zero =>
    exact ⟨0, ⟨(moduleZero_isZero A _).iso
      ((complexYoneda A).map_isZero (isZero_zero _))⟩⟩
  | generator X _ => exact ⟨X, ⟨Iso.refl _⟩⟩
  | shift s c ih =>
    obtain ⟨X, ⟨e⟩⟩ := ih
    exact ⟨X⟦s⟧, ⟨(CategoryTheory.shiftFunctor _ s).mapIso e ≪≫ representableShiftIso A X s⟩⟩
  | sum c d ihc ihd =>
    obtain ⟨X, ⟨e⟩⟩ := ihc
    obtain ⟨Y, ⟨e'⟩⟩ := ihd
    let : PreservesBinaryBiproducts (complexYoneda (C := C) A) :=
      preservesBinaryBiproducts_of_preservesBiproducts _
    exact ⟨X ⊞ Y, ⟨moduleBiprodIso A (CochainComplex C ℤ) _ _ ≪≫ biprod.mapIso e e' ≪≫
      (CategoryTheory.Functor.mapBiprod (complexYoneda A) X Y).symm⟩⟩
  | @cone M N c d f ihc ihd =>
    obtain ⟨X, ⟨e⟩⟩ := ihc
    obtain ⟨Y, ⟨e'⟩⟩ := ihd
    obtain ⟨g, hg⟩ := representableHom_lift A (e.inv ≫ f ≫ e'.hom)
    have h : e.hom ≫ representablePostcompose A g = f ≫ e'.hom := by
      rw [hg]
      simp
    let ae : Arrow.mk f ≅ Arrow.mk (representablePostcompose A g) := Arrow.isoMk e e' h
    let ce := (moduleConeFunctor A (CochainComplex C ℤ)).mapIso ae
    change moduleCone A (CochainComplex C ℤ) f ≅
      moduleCone A (CochainComplex C ℤ) (representablePostcompose A g) at ce
    exact ⟨mappingCone g, ⟨ce ≪≫ representableStandardConeIso A g⟩⟩
  | iso c e ih =>
    obtain ⟨X, ⟨e'⟩⟩ := ih
    exact ⟨X, ⟨e.symm ≪≫ e'⟩⟩

end SerrePositivity.KST.DerivedGeometry.LinearComplex
