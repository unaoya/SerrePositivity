module
public import SerrePositivity.DifferentialGraded.Derived.KFlatBimoduleLocalization
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.KFlatness

/-! # 右相対K-flat部分圏の局所化から導来bimodule圏への対象の到達性

## 概要
右相対K-flat部分圏の局所化から導来bimodule圏への対象の到達性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/KFlatBimoduleReplacement.lean。固定dg圏上の導来tensor・
Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (C : Type v) (E : Type w)
  [DGCategory A C] [DGCategory A E] [Small.{u} C] [Small.{u} E]

def rightKFlatResolutionObj (hE : localHomKFlat A E) (M : BimoduleCategory A C E) :
    RightKFlatBimoduleCategory A C E :=
  ⟨(bimoduleCanonicalSemifreeResolution A C E M).obj,
    (bimoduleCanonicalSemifreeResolution A C E M).rightRelativeKFlat A C E hE⟩

def rightKFlatResolutionDerivedIso (hE : localHomKFlat A E) (M : BimoduleCategory A C E) :
    (rightKFlatDerivedInclusion A C E).obj
        ((rightKFlatToDerived A C E).obj (rightKFlatResolutionObj A C E hE M)) ≅
      (bimoduleToDerived A C E).obj M :=
  bimoduleDerivedIso A C E (bimoduleCanonicalSemifreeResolution A C E M).π
    (bimoduleCanonicalSemifreeResolution A C E M).quasiIso

/-- 本質的全射性のみ。充満忠実性をこの段階では仮定しない。 -/
lemma rightKFlatDerivedInclusion_essSurj (hE : localHomKFlat A E) :
    (rightKFlatDerivedInclusion A C E).EssSurj where
  mem_essImage X := by
    obtain ⟨M, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (bimoduleToDerived A C E) X
    exact ⟨(rightKFlatToDerived A C E).obj (rightKFlatResolutionObj A C E hE M),
      ⟨rightKFlatResolutionDerivedIso A C E hE M ≪≫ e⟩⟩

end SerrePositivity.DifferentialGraded.BimoduleTensor
