module

public import SerrePositivity.KST.Descent.CentralKernelIdentification

/-!
# 中心局所化の台同定の基底変更との両立

## 概要
局所化と可換する係数変更関手を共通核へ制限し、台つき部分圏との同定が可換することを示す。

## 方針
局所化後の自然同型で零性を移し、二つの制限関手の underlying object が同じことを使う。

## 規約
係数変更・局所化の可換性と自己準同型の局所化比較は K0・T2 から供給する明示的な入力。

## 使われ方
論文 (3.6) の Y = S, X における自然な比較と、定理 3.1 の指定引き戻しとの整合性。
-/

@[expose] public section

universe u v w t r

open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.KST.Descent

variable {R : Type r} [CommRing R]
  {C C' : Type u} [Category.{v} C] [Category.{v} C']
  [Preadditive C] [Preadditive C'] [Linear R C] [Linear R C']
  {ι : Type*} {E E' : ι → Type w}
  [∀ i, Category.{t} (E i)] [∀ i, Category.{t} (E' i)]
  [∀ i, Preadditive (E i)] [∀ i, Preadditive (E' i)]
  [∀ i, Linear R (E i)] [∀ i, Linear R (E' i)]
  (loc : ∀ i, C ⥤ E i) (loc' : ∀ i, C' ⥤ E' i)
  (F : C ⥤ C') (M : ∀ i, E i ⥤ E' i) [∀ i, (M i).Additive]
  (comm : ∀ i, F ⋙ loc' i ≅ loc i ⋙ M i)

omit [Preadditive C] [Preadditive C'] in
include M comm in
/-- 概要：局所化と可換する関手は共通局所化核を保つ（論文 (3.6)）。
方針：局所化後の自然同型と加法関手による零対象の保存を使う。
規約：局所化核の保存を独立に仮定しない。使われ方：基底変更の支持核への制限。 -/
theorem centralLocalizationKernel_map (P : C) (hP : centralLocalizationKernel loc P) :
    centralLocalizationKernel loc' (F.obj P) := by
  intro i
  exact ((M i).map_isZero (hP i)).of_iso ((comm i).app P)

/-- 概要：指定係数変更を二つの共通局所化核へ制限する（論文 (3.6)）。
方針：共通核保存の証明で元の関手を充満部分圏へ持ち上げる。
規約：射は元の指定関手 F の像を使う。使われ方：台の同定の自然性の正方形。 -/
def centralKernelMap : (centralLocalizationKernel loc).FullSubcategory ⥤
    (centralLocalizationKernel loc').FullSubcategory :=
  (centralLocalizationKernel loc').lift ((centralLocalizationKernel loc).ι ⋙ F)
    (fun P ↦ centralLocalizationKernel_map loc loc' F M comm P.obj P.property)

variable [F.Additive] [F.Linear R] (z : ι → R)

/-- 概要：指定係数変更を既存の台つき部分圏へ制限する（論文 (3.6)）。
方針：既存の中心台条件の線形関手による保存を使う。
規約：同じ指定関手 F を使う。使われ方：共通核側との関手全体の比較。 -/
def centralScalarSupportMap : (scalarSupported (C := C) z).FullSubcategory ⥤
    (scalarSupported (C := C') z).FullSubcategory :=
  (scalarSupported (C := C') z).lift ((scalarSupported (C := C) z).ι ⋙ F)
    (fun P ↦ scalarSupported_map z F P.obj P.property)

variable [Finite ι] [∀ i, (loc i).Additive] [∀ i, (loc' i).Additive]
  [∀ i, (loc i).Linear R] [∀ i, (loc' i).Linear R]
  [∀ i (P : C), IsLocalizedModule (Submonoid.powers (z i))
    ((loc i).mapLinearMap R : (P ⟶ P) →ₗ[R] _)]
  [∀ i (P : C'), IsLocalizedModule (Submonoid.powers (z i))
    ((loc' i).mapLinearMap R : (P ⟶ P) →ₗ[R] _)]

/-- 概要：中心台の同定は指定係数変更関手と自然同型を通じて可換（論文 (3.6)）。
方針：両経路の元の対象が F.obj P であることから恒等同型を作る。
規約：対象ごとの同型に留めず、全ての射への自然性を保持する。
使われ方：Y = S, X の支持つき比較を定理 3.1 の指定引き戻しへ渡す。 -/
noncomputable def centralKernelScalarEquivalence_naturality :
    centralKernelMap loc loc' F M comm ⋙ (centralKernelScalarEquivalence loc' z).functor ≅
      (centralKernelScalarEquivalence loc z).functor ⋙ centralScalarSupportMap F z :=
  NatIso.ofComponents (fun P ↦ ObjectProperty.isoMk _ (Iso.refl (F.obj P.obj))) (by
    intro P Q f
    apply ObjectProperty.hom_ext
    change F.map f.hom ≫ 𝟙 (F.obj Q.obj) = 𝟙 (F.obj P.obj) ≫ F.map f.hom
    simp)

end SerrePositivity.KST.Descent
