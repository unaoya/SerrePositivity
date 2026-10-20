module
public import SerrePositivity.KST.SConstruction.PerfectDGExtension
public import SerrePositivity.KST.SConstruction.DGModuleExtensionIdentity
public import SerrePositivity.KST.SConstruction.DGFunctorClosedComparison

/-! # 実 Perf dg 延長の恒等比較
概要：恒等入力の実 Perf 延長を、元の Perf 模型の恒等関手と全次数で比較する。
方針：全加群上の単位同型を、同じ Hom 複体を持つ充満 dg 部分圏へ戻す。
規約：対象型の厳密な等号は主張しない。使われ方：K-4d の関手的 Perf 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 恒等入力の実 Perf 延長と元の Perf 対象の、元の閉零射を持つ同型。 -/
def perfectDGExtensionIdentityAt (M : PerfectDGModule A D) :
    ForgetEnrichment.of (Complex A) ((perfectDGExtension A D D (DGFunctor.id D)).obj M) ≅
      ForgetEnrichment.of (Complex A) M where
  hom := (dgModuleExtensionIdentityAt A D M.val).hom
  inv := (dgModuleExtensionIdentityAt A D M.val).inv
  hom_inv_id := (dgModuleExtensionIdentityAt A D M.val).hom_inv_id
  inv_hom_id := (dgModuleExtensionIdentityAt A D M.val).inv_hom_id

/-- Perf 恒等比較は、全 Hom 複体上で元の実 graph 延長と可換。 -/
lemma perfectDGExtensionIdentityAt_naturality (M N : PerfectDGModule A D) :
    (perfectDGExtension A D D (DGFunctor.id D)).map M N ≫
        eHomWhiskerLeft (Complex A)
          (ForgetEnrichment.of (Complex A)
            ((perfectDGExtension A D D (DGFunctor.id D)).obj M))
          (perfectDGExtensionIdentityAt A D N).hom =
      eHomWhiskerRight (Complex A) (perfectDGExtensionIdentityAt A D M).hom
        (ForgetEnrichment.of (Complex A) N) :=
  dgModuleExtensionIdentityAt_naturality A D M.val N.val

/-- 恒等入力の実 Perf 延長から恒等 dg 関手への、単位パラメータの全次数自然比較。 -/
def perfectDGExtensionIdentityComparison :
    GradedNatTrans ((Center.ofBraided (Complex A)).obj (𝟙_ (Complex A)))
      (perfectDGExtension A D D (DGFunctor.id D)) (DGFunctor.id (PerfectDGModule A D)) :=
  dgFunctorClosedComparison A _ _ (fun M => (perfectDGExtensionIdentityAt A D M).hom)
    (fun M N => by
      dsimp only [DGFunctor.id, EnrichedFunctor.id]
      rw [Category.id_comp]
      exact perfectDGExtensionIdentityAt_naturality A D M N)

/-- 恒等入力の実 Perf 延長の単位比較の、全次数自然な逆向き。 -/
def perfectDGExtensionIdentityInverseComparison :
    GradedNatTrans ((Center.ofBraided (Complex A)).obj (𝟙_ (Complex A)))
      (DGFunctor.id (PerfectDGModule A D)) (perfectDGExtension A D D (DGFunctor.id D)) :=
  dgFunctorClosedInverseComparison A _ _ (perfectDGExtensionIdentityAt A D)
    (fun M N => by
      dsimp only [DGFunctor.id, EnrichedFunctor.id]
      rw [Category.id_comp]
      exact perfectDGExtensionIdentityAt_naturality A D M N)

/-- 全加群への包含は元の実単位同型の順射を厳密に回収する。 -/
lemma perfectDGExtensionIdentityAt_inclusion (M : PerfectDGModule A D) :
    (perfectDGModuleInclusion A D Set.univ).onClosed.map
        (perfectDGExtensionIdentityAt A D M).hom =
      (dgModuleExtensionIdentityAt A D M.val).hom := by
  change ForgetEnrichment.homTo (Complex A) (dgModuleExtensionIdentityAt A D M.val).hom ≫
      𝟙 (moduleHom A D ((dgModuleExtension A D D (DGFunctor.id D)).obj M.val) M.val) = _
  exact Category.comp_id _

end SerrePositivity.KST.SConstruction
