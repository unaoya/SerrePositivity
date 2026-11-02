module
public import SerrePositivity.DifferentialGraded.SharedFunctoriality.DGModuleExtensionInputTransport

/-! # 実延長比較の入力等号に関する整合性
概要：入力の等号移送を合成比較の前後へ動かす式を固定する。
方針：等号帰納により、元の恒等射と関手の恒等射保存へ帰着する。
規約：等号移送を省略しない。使われ方：元の四入力五角の貼り合わせ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]

/-- 入力等号の連続移送は、元の等号の推移律による移送と一致する。 -/
lemma dgModuleExtensionInputIso_trans {F G H : DGFunctor A D E}
    (h : F = G) (k : G = H) (M : RightModule A D) :
    (dgModuleExtensionInputIso A D E h M).hom ≫
        (dgModuleExtensionInputIso A D E k M).hom =
      (dgModuleExtensionInputIso A D E (h.trans k) M).hom := by
  cases h
  cases k
  simp only [dgModuleExtensionInputIso, eqToIso_refl, Iso.refl_hom]
  exact Category.comp_id _

/-- 元の入力等号による対象比較は、元の閉零射について自然。 -/
lemma dgModuleExtensionInputIso_closed_naturality {F G : DGFunctor A D E}
    (h : F = G) {M N : RightModule A D}
    (f : ForgetEnrichment.of (Complex A) M ⟶ ForgetEnrichment.of (Complex A) N) :
    (dgModuleExtension A D E F).onClosed.map
        (X := ForgetEnrichment.of (Complex A) M)
        (Y := ForgetEnrichment.of (Complex A) N) f ≫
        (dgModuleExtensionInputIso A D E h N).hom =
      (dgModuleExtensionInputIso A D E h M).hom ≫
        (dgModuleExtension A D E G).onClosed.map
        (X := ForgetEnrichment.of (Complex A) M)
        (Y := ForgetEnrichment.of (Complex A) N) f := by
  cases h
  simp only [dgModuleExtensionInputIso, eqToIso_refl, Iso.refl_hom]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

variable (T : Type z) [DGCategory A T] [Small.{u} T]

/-- 第一入力の等号移送は、元の二回延長比較と可換。 -/
lemma dgModuleExtensionCompositionAt_input_left {F F' : DGFunctor A D E}
    (h : F = F') (G : DGFunctor A E T) (M : RightModule A D) :
    (dgModuleExtension A E T G).onClosed.map
        (X := ForgetEnrichment.of (Complex A) ((dgModuleExtension A D E F).obj M))
        (Y := ForgetEnrichment.of (Complex A) ((dgModuleExtension A D E F').obj M))
        (dgModuleExtensionInputIso A D E h M).hom ≫
      (dgModuleExtensionCompositionAt A D E T F' G M).hom =
    (dgModuleExtensionCompositionAt A D E T F G M).hom ≫
      (dgModuleExtensionInputIso A D T (F := F.comp G) (G := F'.comp G)
        (congrArg (fun K => K.comp G) h) M).hom := by
  cases h
  simp only [dgModuleExtensionInputIso, eqToIso_refl, Iso.refl_hom,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

/-- 第二入力の等号移送も、元の二回延長比較と可換。 -/
lemma dgModuleExtensionCompositionAt_input_right (F : DGFunctor A D E)
    {G G' : DGFunctor A E T} (h : G = G') (M : RightModule A D) :
    (dgModuleExtensionInputIso A E T h ((dgModuleExtension A D E F).obj M)).hom ≫
      (dgModuleExtensionCompositionAt A D E T F G' M).hom =
    (dgModuleExtensionCompositionAt A D E T F G M).hom ≫
      (dgModuleExtensionInputIso A D T (congrArg (fun K => F.comp K) h) M).hom := by
  cases h
  simp only [dgModuleExtensionInputIso, eqToIso_refl, Iso.refl_hom,
    Category.id_comp, Category.comp_id]

end SerrePositivity.KST.SConstruction
