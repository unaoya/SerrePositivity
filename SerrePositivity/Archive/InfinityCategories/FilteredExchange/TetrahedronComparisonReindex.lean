module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoComponentPre
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.VertexIsoCompositionTransport
public import Mathlib.CategoryTheory.CommSq

/-!
概要：同じ六辺・四面の指定比較を、二つの全相対始域の間の厳密な制限で保持する。
方針：六可換四角形と元の四つの指定成分の自然性を束ねる。
規約：三単体の合成関係を仮定しない。使われ方：全係数上の指定関係からの反映。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の四面の指定値を保つ、六辺について厳密に可換な全始域の制限データ。 -/
structure TetrahedronComparisonReindex (X₀ X₁ X₂ X₃ Y₀ Y₁ Y₂ Y₃ : SSet.{u})
    [Quasicategory X₀] [Quasicategory X₁] [Quasicategory X₂] [Quasicategory X₃]
    [Quasicategory Y₀] [Quasicategory Y₁] [Quasicategory Y₂] [Quasicategory Y₃] where
  old01 : X₀ ⟶ X₁
  old12 : X₁ ⟶ X₂
  old23 : X₂ ⟶ X₃
  old02 : X₀ ⟶ X₂
  old13 : X₁ ⟶ X₃
  old03 : X₀ ⟶ X₃
  new01 : Y₀ ⟶ Y₁
  new12 : Y₁ ⟶ Y₂
  new23 : Y₂ ⟶ Y₃
  new02 : Y₀ ⟶ Y₂
  new13 : Y₁ ⟶ Y₃
  new03 : Y₀ ⟶ Y₃
  r0 : X₀ ⟶ Y₀
  r1 : X₁ ⟶ Y₁
  r2 : X₂ ⟶ Y₂
  r3 : X₃ ⟶ Y₃
  old012 : FunctorIso old02 (old01 ≫ old12)
  old123 : FunctorIso old13 (old12 ≫ old23)
  old013 : FunctorIso old03 (old01 ≫ old13)
  old023 : FunctorIso old03 (old02 ≫ old23)
  new012 : FunctorIso new02 (new01 ≫ new12)
  new123 : FunctorIso new13 (new12 ≫ new23)
  new013 : FunctorIso new03 (new01 ≫ new13)
  new023 : FunctorIso new03 (new02 ≫ new23)
  comm01 : CommSq old01 r0 r1 new01
  comm12 : CommSq old12 r1 r2 new12
  comm23 : CommSq old23 r2 r3 new23
  comm02 : CommSq old02 r0 r2 new02
  comm13 : CommSq old13 r1 r3 new13
  comm03 : CommSq old03 r0 r3 new03
  value012 (x : X₀ _⦋0⦌) :
    HEq (VertexIso.map (old012.app x) r2) (new012.app (r0.app _ x))
  value123 (x : X₁ _⦋0⦌) :
    HEq (VertexIso.map (old123.app x) r3) (new123.app (r1.app _ x))
  value013 (x : X₀ _⦋0⦌) :
    HEq (VertexIso.map (old013.app x) r3) (new013.app (r0.app _ x))
  value023 (x : X₀ _⦋0⦌) :
    HEq (VertexIso.map (old023.app x) r3) (new023.app (r0.app _ x))

end SerrePositivity.InfinityCategories.F2
