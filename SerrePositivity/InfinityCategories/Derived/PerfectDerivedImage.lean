module
public import SerrePositivity.InfinityCategories.Derived.PerfectImage
public import SerrePositivity.InfinityCategories.Derived.PerfectCanonicalHomotopy

/-! # h Perf の導来圏における像

概要：h Perf の標準包含の像は有界有限射影複体の導来像と一致する。
方針：D3 の同値と複体ホモトピー圏での本質像の同定を合成する。
規約：HasDerivedCategory は D3 と同じ選択。使われ方：G2 の完全対象の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (S : Type u) [CommRing S] [HasDerivedCategory.{w} (ModuleCat.{u} S)]

/-- 概要：h Perf の包含の導来比較像は、複体ホモトピー比較像の局所化と同型である。
方針：N3 の比較の余単位を導来関手で写し、標準包含との比較を合成する。
規約：D3 の同値を用いる。使われ方：導来像の具体的計算。 -/
def perfectCanonicalDerivedIso (Y : perfectInfinityHomotopyCategory S) :
    (derivedInfinityHomotopyEquivalence S).functor.obj
      ((perfectCanonicalHomotopyInclusion S).obj Y) ≅
        DerivedCategory.Qh.obj ((perfectComplexHomotopyInclusion S).obj Y) :=
  (derivedInfinityHomotopyEquivalence S).functor.mapIso
      ((perfectHomotopyInclusionIso S).app Y) ≪≫
    (semifreeDerivedEquivalence S).functor.mapIso
      ((derivedInfinityH0Equivalence S).counitIso.app
        ((perfectH0Inclusion S).obj ((perfectInfinityH0Equivalence S).functor.obj Y)))

/-- 概要：h D(S) の対象が h Perf の標準包含の像にあることは、有限射影複体の導来像を持つことと同値。
方針：複体ホモトピー圏での本質像を局所化し、逆向きは D3 の充満忠実性で持ち上げる。
規約：同型閉包を含む本質像の一致。使われ方：h Perf の充満部分圏としての主定理。 -/
theorem perfectCanonicalHomotopyInclusion_essImage_iff
    (X : derivedInfinityHomotopyCategory S) :
    (∃ Y : perfectInfinityHomotopyCategory S,
      Nonempty ((perfectCanonicalHomotopyInclusion S).obj Y ≅ X)) ↔
        ∃ K : Complex S, strictlyPerfectComplex S K ∧
          Nonempty ((derivedInfinityHomotopyEquivalence S).functor.obj X ≅
            DerivedCategory.Q.obj K) := by
  constructor
  · rintro ⟨Y, ⟨e⟩⟩
    obtain ⟨K, hK, ⟨eK⟩⟩ := (complexPerfectModel_iff S
      ((perfectComplexHomotopyInclusion S).obj Y).as).1
        (perfectComplexHomotopyInclusion_obj S Y)
    exact ⟨K, hK, ⟨(derivedInfinityHomotopyEquivalence S).functor.mapIso e.symm ≪≫
      perfectCanonicalDerivedIso S Y ≪≫ DerivedCategory.Qh.mapIso eK ≪≫
        (DerivedCategory.quotientCompQhIso (ModuleCat S)).app K⟩⟩
  · rintro ⟨K, hK, ⟨e⟩⟩
    obtain ⟨Y, ⟨eY⟩⟩ := (perfectComplexHomotopyInclusion_essImage_iff S
      ((HomotopyCategory.quotient _ _).obj K)).2 (complexPerfectModel_of_strict S hK)
    exact ⟨Y, ⟨(derivedInfinityHomotopyEquivalence S).functor.preimageIso
      (perfectCanonicalDerivedIso S Y ≪≫ DerivedCategory.Qh.mapIso eY ≪≫
        (DerivedCategory.quotientCompQhIso (ModuleCat S)).app K ≪≫ e.symm)⟩⟩

end SerrePositivity.InfinityCategories
