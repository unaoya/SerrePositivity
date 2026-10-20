module
public import SerrePositivity.KST.SConstruction.DGFunctorClosedNaturality
public import SerrePositivity.KST.SConstruction.DGModuleExtensionInputTransport

/-! # 元の実延長比較の閉零自然性
概要：合成比較の全 Hom 自然性を、元の加群射の可換四角形へ制限する。
方針：単位からの Hom 元を使い、二回の閉零作用と元の合成作用を照合する。
規約：比較射と対象は元のものを使う。使われ方：四入力の五角の辺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w) (T : Type z)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
  [DGCategory A T] [Small.{u} T] (F : DGFunctor A D E) (G : DGFunctor A E T)

/-- 元の加群射に対する、実延長の合成比較の自然性。 -/
lemma dgModuleExtensionCompositionAt_closed_naturality
    {M N : RightModule A D}
    (f : ForgetEnrichment.of (Complex A) M ⟶ ForgetEnrichment.of (Complex A) N) :
    (dgModuleExtension A E T G).onClosed.map
        ((dgModuleExtension A D E F).onClosed.map f) ≫
      (dgModuleExtensionCompositionAt A D E T F G N).hom =
    (dgModuleExtensionCompositionAt A D E T F G M).hom ≫
      (dgModuleExtension A D T (F.comp G)).onClosed.map f := by
  exact dgFunctorClosedComparison_naturality A
    ((dgModuleExtension A D E F).comp (dgModuleExtension A E T G))
    (dgModuleExtension A D T (F.comp G))
    (fun M => (dgModuleExtensionCompositionAt A D E T F G M).hom)
    (dgModuleExtensionCompositionAt_naturality A D E T F G) f

/-- 全 Hom 比較を変更せず通常の閉零射圏の自然同型に束ねる。 -/
def dgModuleExtensionCompositionClosedIso :
    (dgModuleExtension A D E F).onClosed ⋙ (dgModuleExtension A E T G).onClosed ≅
      (dgModuleExtension A D T (F.comp G)).onClosed :=
  NatIso.ofComponents (dgModuleExtensionCompositionAt A D E T F G)
    (fun f => dgModuleExtensionCompositionAt_closed_naturality A D E T F G f)

end SerrePositivity.KST.SConstruction
