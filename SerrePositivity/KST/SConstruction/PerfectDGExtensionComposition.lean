module
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionIdentity
public import SerrePositivity.DifferentialGraded.SharedFunctoriality.DGModuleExtensionComposition

/-! # 実 Perf dg 延長の合成比較
概要：二回の実 Perf 延長と、合成入力の一回の実 Perf 延長を全次数で比較する。
方針：元の実加群同型を充満 dg 部分圏へ戻し、順逆の豊穣自然変換に束ねる。
規約：合成の厳密な等号や高次 coherence は別工程。使われ方：K-4d の関手的 Perf 模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w) (T : Type z)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
  [DGCategory A T] [Small.{u} T] (F : DGFunctor A D E) (G : DGFunctor A E T)

/-- 反復した実 Perf 延長から合成入力の実 Perf 延長への元の閉零同型。 -/
def perfectDGExtensionCompositionAt (M : PerfectDGModule A D) :
    ForgetEnrichment.of (Complex A)
        (((perfectDGExtension A D E F).comp (perfectDGExtension A E T G)).obj M) ≅
      ForgetEnrichment.of (Complex A) ((perfectDGExtension A D T (F.comp G)).obj M) where
  hom := (dgModuleExtensionCompositionAt A D E T F G M.val).hom
  inv := (dgModuleExtensionCompositionAt A D E T F G M.val).inv
  hom_inv_id := (dgModuleExtensionCompositionAt A D E T F G M.val).hom_inv_id
  inv_hom_id := (dgModuleExtensionCompositionAt A D E T F G M.val).inv_hom_id

/-- 実 Perf 延長の合成比較は、全 Hom 複体上で自然。 -/
lemma perfectDGExtensionCompositionAt_naturality (M N : PerfectDGModule A D) :
    ((perfectDGExtension A D E F).comp (perfectDGExtension A E T G)).map M N ≫
        eHomWhiskerLeft (Complex A)
          (ForgetEnrichment.of (Complex A)
            (((perfectDGExtension A D E F).comp (perfectDGExtension A E T G)).obj M))
          (perfectDGExtensionCompositionAt A D E T F G N).hom =
      (perfectDGExtension A D T (F.comp G)).map M N ≫
        eHomWhiskerRight (Complex A) (perfectDGExtensionCompositionAt A D E T F G M).hom
          (ForgetEnrichment.of (Complex A) ((perfectDGExtension A D T (F.comp G)).obj N)) :=
  dgModuleExtensionCompositionAt_naturality A D E T F G M.val N.val

/-- 合成入力への実 Perf 比較の、単位パラメータの全次数自然変換。 -/
def perfectDGExtensionCompositionComparison :
    GradedNatTrans ((Center.ofBraided (Complex A)).obj (𝟙_ (Complex A)))
      ((perfectDGExtension A D E F).comp (perfectDGExtension A E T G))
      (perfectDGExtension A D T (F.comp G)) :=
  dgFunctorClosedComparison A _ _
    (fun M => (perfectDGExtensionCompositionAt A D E T F G M).hom)
    (perfectDGExtensionCompositionAt_naturality A D E T F G)

/-- 同じ実 Perf 合成比較の、全次数自然な逆向き。 -/
def perfectDGExtensionCompositionInverseComparison :
    GradedNatTrans ((Center.ofBraided (Complex A)).obj (𝟙_ (Complex A)))
      (perfectDGExtension A D T (F.comp G))
      ((perfectDGExtension A D E F).comp (perfectDGExtension A E T G)) :=
  dgFunctorClosedInverseComparison A _ _ (perfectDGExtensionCompositionAt A D E T F G)
    (perfectDGExtensionCompositionAt_naturality A D E T F G)

/-- 全加群への包含は、元の実 graph 合成比較の順射を厳密に回収する。 -/
lemma perfectDGExtensionCompositionAt_inclusion (M : PerfectDGModule A D) :
    (perfectDGModuleInclusion A T Set.univ).onClosed.map
        (perfectDGExtensionCompositionAt A D E T F G M).hom =
      (dgModuleExtensionCompositionAt A D E T F G M.val).hom := by
  change ForgetEnrichment.homTo (Complex A)
      (dgModuleExtensionCompositionAt A D E T F G M.val).hom ≫
      𝟙 (moduleHom A T
        ((dgModuleExtension A E T G).obj ((dgModuleExtension A D E F).obj M.val))
        ((dgModuleExtension A D T (F.comp G)).obj M.val)) = _
  exact Category.comp_id _

end SerrePositivity.KST.SConstruction
