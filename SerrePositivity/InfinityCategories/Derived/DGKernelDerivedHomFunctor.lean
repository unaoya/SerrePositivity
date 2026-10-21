module
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedIsoAlgebra
/-!
概要：任意の双加群射を、元の導来 kernel 作用間の全関手射へ送る。
方針：通常 tensor の射作用を元の raw factor 同型で共役する。
規約：対象は同じ導来作用。使われ方：非可逆射と模型変更の自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 通常 tensor の射作用を、半自由入力制限と同じ出力分解へ送る関手。 -/
def dgKernelResolvedRawFunctorHomFunctor :
    BimoduleCategory R E D ⥤
      hoFunctor.obj ((ihom (dgModuleDerivedInfinityCategory R D)).obj
        (dgModuleDerivedInfinityCategory R E)) :=
  dgKernelTensorFunctorHomFunctor R D E ⋙
    SSet.mapHomotopyCategory
      ((pre (dgNerve.map
        (dgFullSubcategoryInclusion R (RightModule R D) (dgModuleSemifreeProperty R D)))).app
        (dgModuleNerve R E)) ⋙
    SSet.mapHomotopyCategory ((ihom (dgModuleDerivedInfinityCategory R D)).map
      (dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id (RightModule R E))))
/-- 元の kernel 導来作用と、指定 raw 分解作用との同じ比較。 -/
def dgKernelDerivedRawFactorIso (P : BimoduleCategory R E D) :
    SSet.HomotopyCategory.mk (functorVertex
      (dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D P))) ≅
      (dgKernelResolvedRawFunctorHomFunctor R D E).obj P := by
  have e := dgModuleResolvedInfinity_rawFactorIso R (SemifreeDGModules R D) E
    (dgSemifreeKernelModuleDG R D E (BimoduleCategory.underlying R E D P))
  simpa only [dgKernelResolvedRawFunctorHomFunctor, dgSemifreeKernelModuleDG,
    dgNerve.map_comp, Category.assoc] using! e
/-- 任意の双加群射による、同じ実導来作用の h Fun 値関手。 -/
def dgKernelDerivedFunctorHomFunctor :
    BimoduleCategory R E D ⥤
      hoFunctor.obj ((ihom (dgModuleDerivedInfinityCategory R D)).obj
        (dgModuleDerivedInfinityCategory R E)) where
  obj P := SSet.HomotopyCategory.mk (functorVertex
    (dgKernelDerivedInfinity R D E (BimoduleCategory.underlying R E D P)))
  map {P Q} f :=
    (dgKernelDerivedRawFactorIso R D E P).hom ≫
      (dgKernelResolvedRawFunctorHomFunctor R D E).map f ≫
      (dgKernelDerivedRawFactorIso R D E Q).inv
  map_id P := by
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id]
  map_comp {P Q S} f g := by
    rw [CategoryTheory.Functor.map_comp]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
/-- 同じ関手の同型像は、元の指定双加群同型の作用そのもの。 -/
lemma dgKernelDerivedFunctorHomFunctor_mapIso {P Q : BimoduleCategory R E D} (e : P ≅ Q) :
    (dgKernelDerivedFunctorHomFunctor R D E).mapIso e =
      dgKernelDerivedInfinity_bimoduleIso R D E e := by
  apply Iso.ext
  change (dgKernelDerivedRawFactorIso R D E P).hom ≫
    (dgKernelResolvedRawFunctorHomFunctor R D E).map e.hom ≫
      (dgKernelDerivedRawFactorIso R D E Q).inv = _
  unfold dgKernelDerivedInfinity_bimoduleIso dgModuleResolvedInfinity_isoOfRawFunctorIso
  simp only [Iso.trans_hom, Iso.symm_hom]
  congr 1
  change (((dgKernelResolvedRawFunctorHomFunctor R D E).mapIso e).hom) ≫ _ = _
  congr 1
  change ((SSet.mapHomotopyCategory
    ((ihom (dgModuleDerivedInfinityCategory R D)).map
      (dgModuleResolvedInfinity R (RightModule R E) E (DGFunctor.id (RightModule R E))))).mapIso
    ((SSet.mapHomotopyCategory
      ((pre (dgNerve.map
        (dgFullSubcategoryInclusion R (RightModule R D) (dgModuleSemifreeProperty R D)))).app
          (dgModuleNerve R E))).mapIso ((dgKernelTensorFunctorHomFunctor R D E).mapIso e))).hom = _
  rw [dgKernelTensorFunctorHomFunctor_mapIso]
  rfl
end
end SerrePositivity.InfinityCategories
