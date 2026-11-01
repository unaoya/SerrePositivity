module
public import SerrePositivity.InfinityCategories.Derived.DGModuleStability
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedLimitTransfer
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedZeroObjects
public import SerrePositivity.InfinityCategories.Derived.DGSemifreeRawFunctorExact
public import SerrePositivity.InfinityCategories.Derived.DGKernelDerivedInfinity
/-!
概要：一般 dg 加群関手の同じ実導来作用と、任意 kernel の同じ ∞ 作用の完全性を結論する。
方針：零頂点を保存し、生の cofiber 像の引き戻し性を全 Hom 試験で半自由出力へ戻す。
規約：生の出力の射影性・局所 Hom 平坦性は追加しない。使われ方：一般 RHom の ∞ 随伴。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 同じ一般 dg 関手の実分解後の cofiber 保存。 -/
lemma dgModuleResolvedFunctor_isExactFunctor
    (F : DGFunctor R (RightModule R D) (RightModule R E)) :
    IsExactFunctor (dgModuleResolvedInfinity R (SemifreeDGModules R D) E
      ((dgFullSubcategoryInclusion R (RightModule R D)
        (dgModuleSemifreeProperty R D)).comp F)) where
  preservesZero := dgModuleResolvedInfinity_preservesZeroVertices R (SemifreeDGModules R D) E _
  preservesCofiber t ht := by
    let := dgModuleDerivedInfinityCategory_isStable R E
    let := dgSemifreeModuleFunctorRaw_isExactFunctor R D E F
    have h := IsExactFunctor.preservesCofiber
      (F := dgNerve.map ((dgFullSubcategoryInclusion R (RightModule R D)
        (dgModuleSemifreeProperty R D)).comp F)) t ht
    apply IsStable.pushout_of_pullback_square
    apply dgModuleResolvedInfinity_isPullbackSquare_of_raw R (SemifreeDGModules R D) E _
    exact IsStable.pullback_of_pushout_square _ h
/-- 同じ一般 dg 関手の実分解後の cofiber 保存。 -/
lemma dgKernelDerivedInfinity_isExactFunctor (P : Bimodule R E D) :
    IsExactFunctor (dgKernelDerivedInfinity R D E P) :=
  dgModuleResolvedFunctor_isExactFunctor R D E (Morita.kernelTensor R D E P)
end SerrePositivity.InfinityCategories
