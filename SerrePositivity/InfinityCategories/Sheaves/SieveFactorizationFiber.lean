module

public import SerrePositivity.InfinityCategories.Sheaves.SieveFactorization
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
概要：二段分解の中間射を固定した fiber と引き戻し篩の比較。
方針：合成射と Over の可換三角形を相互に回収する。
  文献対応：HTT 6.2.2.6 の篩に沿う降下の合成。係数の極限存在は仮定しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {U : C}

/-- 中間射 t を固定した二段分解の圏。 -/
abbrev sieveFactorizationFiber (R S : Sieve U) (t : sieveCategory R) :=
  CostructuredArrow (ObjectProperty.ι (fun f : Over U => (R ⊓ S).arrows f.hom)) t.obj

/-- 引き戻し篩の射 a を、合成 a ≫ t と t への三角形へ送る。 -/
def pullbackSieveToFactorizationFiber (R S : Sieve U) (t : sieveCategory R) :
    sieveCategory (S.pullback t.obj.hom) ⥤ sieveFactorizationFiber R S t where
  obj A :=
    { left := ⟨Over.mk (A.obj.hom ≫ t.obj.hom),
        ⟨R.downward_closed t.property A.obj.hom, A.property⟩⟩
      right := ⟨⟨⟩⟩
      hom := Over.homMk A.obj.hom }
  map f := CostructuredArrow.homMk
    (ObjectProperty.homMk (Over.homMk f.hom.left (by
      change f.hom.left ≫ (_ ≫ _) = _ ≫ _
      rw [← Category.assoc, Over.w f.hom]))) (by
        apply Over.OverMorphism.ext
        exact Over.w f.hom)
  map_id A := by
    apply CostructuredArrow.hom_ext
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    rfl
  map_comp f g := by
    apply CostructuredArrow.hom_ext
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    rfl

/-- 比較は元の全射を忠実に保持する。 -/
instance pullbackSieveToFactorizationFiber_faithful (R S : Sieve U)
    (t : sieveCategory R) : (pullbackSieveToFactorizationFiber R S t).Faithful where
  map_injective {A B} f g h := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact congrArg (fun z => z.left.hom.left) h

/-- 可換三角形の射は、引き戻し篩の射に一意に戻る。 -/
instance pullbackSieveToFactorizationFiber_full (R S : Sieve U)
    (t : sieveCategory R) : (pullbackSieveToFactorizationFiber R S t).Full where
  map_surjective {A B} f := by
    have hw := congrArg (fun z => z.left) (CostructuredArrow.w f)
    change f.left.hom.left ≫ B.obj.hom = A.obj.hom at hw
    refine ⟨ObjectProperty.homMk (Over.homMk f.left.hom.left hw), ?_⟩
    apply CostructuredArrow.hom_ext
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    rfl

/-- 各三角形は、その第一の射から作った分解と同型である。 -/
instance pullbackSieveToFactorizationFiber_essSurj (R S : Sieve U)
    (t : sieveCategory R) : (pullbackSieveToFactorizationFiber R S t).EssSurj where
  mem_essImage B := by
    let A : sieveCategory (S.pullback t.obj.hom) :=
      ⟨Over.mk B.hom.left, by
        change S.arrows (B.hom.left ≫ t.obj.hom)
        rw [Over.w B.hom]
        exact B.left.property.2⟩
    let i : ((pullbackSieveToFactorizationFiber R S t).obj A).left.obj ≅ B.left.obj := by
      change Over.mk (B.hom.left ≫ t.obj.hom) ≅ B.left.obj
      exact Over.isoMk (Iso.refl _) (by simpa using (Over.w B.hom).symm)
    refine ⟨A, ⟨CostructuredArrow.isoMk (ObjectProperty.isoMk _ i) ?_⟩⟩
    apply Over.OverMorphism.ext
    exact Category.id_comp _

/-- 中間射を固定した全 fiber は、引き戻し篩の元の圏と同値。 -/
def pullbackSieveFactorizationFiberEquivalence (R S : Sieve U) (t : sieveCategory R) :
    sieveCategory (S.pullback t.obj.hom) ≌ sieveFactorizationFiber R S t := by
  letI : (pullbackSieveToFactorizationFiber R S t).IsEquivalence := {}
  exact (pullbackSieveToFactorizationFiber R S t).asEquivalence

end SerrePositivity.InfinityCategories.Sheaves
