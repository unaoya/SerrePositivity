module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Quotient
public import SerrePositivity.CommutativeAlgebra.QuotientScalarExtension
public import SerrePositivity.BhattScholze.Andre.Transfinite.CompleteFlatColimit
public import SerrePositivity.BhattScholze.Andre.Transfinite.FaithfullyFlatColimit
/-! # 剰余テンソルの余極限比較と完全忠実平坦性の保存

BS Thm 7.14（著者版 p.61）の極限段に用いる。固定基底の I 完全忠実平坦な代数の
有向余極限が I 完全忠実平坦であることを、元の R/I 作用のまま証明する。
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre.Transfinite
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A ι : Type u} [CommRing A] [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra A (S i)]
    (f : ∀ i j, i ≤ j → S i →ₐ[A] S j) [DirectedSystem S (fun i j h ↦ f i j h)]
/-- ## 概要
代数の有向系の、元の基底上の加群図式。BS Thm 7.14（著者版 p.61）の極限段の補助対象。

## 方針
遷移代数準同型をそのまま線形写像とし、DirectedSystem の法則から函手の法則を示す。

## 規約
基底 A の作用を保つ。

## 使われ方
剰余テンソル函手に余極限の普遍性を適用する。
-/
def algebraModuleDiagram : ι ⥤ ModuleCat.{u} A where
  obj i := ModuleCat.of A (S i)
  map h := ModuleCat.ofHom (f _ _ h.le).toLinearMap
  map_id i := by
    ext x
    exact DirectedSystem.map_self (f := fun i j h ↦ f i j h) x
  map_comp hij hjk := by
    ext x
    exact (DirectedSystem.map_map (f := fun i j h ↦ f i j h) hij.le hjk.le x).symm

/-- ## 概要
非交和モデルの代数余極限を頂点とする加群余錐。BS Thm 7.14（著者版 p.61）の補助対象。

## 方針
標準包含の両立性から余錐を構成する。

## 規約
環と加群の余極限の台集合だけでなく、元の A 作用を指定する。

## 使われ方
スカラー拡大で保存される具体的余錐として使う。
-/
def algebraModuleCocone : Cocone (algebraModuleDiagram S f) where
  pt := ModuleCat.of A (_root_.DirectLimit S f)
  ι := {
    app := fun i ↦ ModuleCat.ofHom (DirectLimit.Module.of A ι S f i)
    naturality := by
      intro i j h
      ext x
      exact DirectLimit.Module.of_f }

/-- ## 概要
代数余極限の標準加群余錐は余極限である。BS Thm 7.14（著者版 p.61）の極限段の補助命題。

## 方針
非交和モデルの線形な普遍写像を使い、包含との合成で一意性を検査する。

## 規約
追加の平坦性や単射性を仮定しない。

## 使われ方
剰余スカラー拡大による余極限保存に使う。
-/
def algebraModuleIsColimit : IsColimit (algebraModuleCocone S f) where
  desc c := ModuleCat.ofHom (DirectLimit.Module.lift A ι S f (fun i ↦ (c.ι.app i).hom)
    (fun i j h x ↦ by
      have hc := congrArg (fun g ↦ g.hom x) (c.w (homOfLE h))
      exact hc))
  fac c i := by ext x; rfl
  uniq c m hm := by
    apply ModuleCat.hom_ext
    apply DirectLimit.Module.hom_ext
    intro i
    ext x
    exact congrArg (fun g ↦ g.hom x) (hm i)



open SerrePositivity
attribute [local instance] adicQuotientAlgebra
variable (I : Ideal A)
/-- ## 概要
基底イデアル I による各段の剰余環を結ぶ R/I 代数準同型。
BS Thm 7.14（著者版 p.61）の極限段の剰余図式を構成する。

## 方針
元の代数準同型の基底との両立性から、拡張イデアルを剰余する。

## 規約
剰余環の R/I 作用は既存の adicQuotientAlgebra。

## 使われ方
剰余環の有向余極限と、余極限の剰余テンソルを比較する。
-/
def residueTransition (i j : ι) (h : i ≤ j) :
    S i ⧸ I.map (algebraMap A (S i)) →ₐ[A ⧸ I] S j ⧸ I.map (algebraMap A (S j)) :=
  { Ideal.quotientMap (I.map (algebraMap A (S j))) (f i j h).toRingHom (by
      apply Ideal.map_le_iff_le_comap.mpr
      intro r hr
      change f i j h (algebraMap A (S i) r) ∈ I.map (algebraMap A (S j))
      rw [(f i j h).commutes]
      exact Ideal.mem_map_of_mem (algebraMap A (S j)) hr) with
    commutes' := by
      intro q
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
      change Ideal.Quotient.mk _ (f i j h (algebraMap A (S i) r)) =
        Ideal.Quotient.mk _ (algebraMap A (S j) r)
      rw [(f i j h).commutes] }
/-- ## 概要
剰余環の遷移写像は有向系を成す。BS Thm 7.14（著者版 p.61）の極限段の補助命題。

## 方針
剰余代表元上で元の有向系の恒等・合成法則を適用する。

## 規約
遷移写像は residueTransition で固定する。

## 使われ方
通常忠実平坦な剰余代数の有向余極限を構成する。
-/
instance residueDirectedSystem :
    DirectedSystem (fun i ↦ S i ⧸ I.map (algebraMap A (S i)))
      (fun i j h ↦ residueTransition S f I i j h) where
  map_self := by
    intro i x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ (f i i le_rfl x) = Ideal.Quotient.mk _ x
    rw [DirectedSystem.map_self' f]
  map_map := by
    intro k j i hij hjk x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ (f j k hjk (f i j hij x)) =
      Ideal.Quotient.mk _ (f i k (hij.trans hjk) x)
    rw [DirectedSystem.map_map (f := fun i j h ↦ f i j h)]

/-- ## 概要
加群図式の剰余スカラー拡大と、通常の剰余環図式は自然同型。
BS Thm 7.14（著者版 p.61）の極限段の比較。

## 方針
既存の quotientAlgebraScalarExtensionEquiv の自然性を、実際の剰余遷移写像と照合する。

## 規約
R/I 線形性を保持し、R 線形性だけに弱めない。

## 使われ方
スカラー拡大で保存した余極限を剰余環の余極限と同定する。
-/
def residueDiagramIso : algebraModuleDiagram S f ⋙ ModuleCat.extendScalars (Ideal.Quotient.mk I) ≅
    algebraModuleDiagram (fun i ↦ S i ⧸ I.map (algebraMap A (S i))) (residueTransition S f I) := by
  refine NatIso.ofComponents
    (fun i ↦ (quotientAlgebraScalarExtensionEquiv I (S i)).toModuleIso) ?_
  intro i j h
  have he : ModuleCat.ofHom (adicAlgebraReductionMap I (f i j h.le)) =
      ModuleCat.ofHom (residueTransition S f I i j h.le).toLinearMap := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change adicAlgebraReductionMap I (f i j h.le) (Ideal.Quotient.mk _ x) =
      residueTransition S f I i j h.le (Ideal.Quotient.mk _ x)
    rw [adicAlgebraReductionMap_mk]
    rfl
  simpa only [algebraModuleDiagram, Functor.comp_map, he] using
    quotientAlgebraScalarExtensionEquiv_naturality I (f i j h.le)


/-- ## 概要
有向余極限の通常剰余テンソルは、各段の通常剰余環の有向余極限と R/I 上線形同型。
BS Thm 7.14（著者版 p.61）の極限段の忠実性に用いる。

## 方針
加群余錐の普遍性をスカラー拡大で保存し、既存の剰余自然同型と組み合わせる。
元の剰余テンソルへの比較も既存の環商・テンソル同型で与える。

## 規約
元の R/I 作用を保つ。I は任意で、有限生成性・単射性・平坦性は要求しない。

## 使われ方
剰余環の余極限の忠実平坦性を、定義に現れる剰余テンソルへ移送する。
-/
def residueTensorDirectLimitEquiv :
    ((A ⧸ I) ⊗[A] (_root_.DirectLimit S f)) ≃ₗ[A ⧸ I]
      (_root_.DirectLimit (fun i ↦ S i ⧸ I.map (algebraMap A (S i)))
        (residueTransition S f I)) := by
  let E := ModuleCat.extendScalars (Ideal.Quotient.mk I)
  let F := algebraModuleDiagram S f
  let B := fun i ↦ S i ⧸ I.map (algebraMap A (S i))
  let g := residueTransition S f I
  let e1 : E.obj (ModuleCat.of A (_root_.DirectLimit S f)) ≅ colimit (F ⋙ E) :=
    (isColimitOfPreserves E (algebraModuleIsColimit S f)).coconePointUniqueUpToIso
      (colimit.isColimit _)
  let e2 : colimit (F ⋙ E) ≅ colimit (algebraModuleDiagram B g) :=
    HasColimit.isoOfNatIso (residueDiagramIso S f I)
  let e3 : colimit (algebraModuleDiagram B g) ≅ ModuleCat.of (A ⧸ I) (_root_.DirectLimit B g) :=
    colimit.isoColimitCocone ⟨_, algebraModuleIsColimit B g⟩
  let e : ((E.obj (ModuleCat.of A (_root_.DirectLimit S f))) : Type u) ≃ₗ[A ⧸ I]
      ((A ⧸ I) ⊗[A] (_root_.DirectLimit S f)) :=
    (quotientAlgebraScalarExtensionEquiv I (_root_.DirectLimit S f)).trans
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (_root_.DirectLimit S f) I).toLinearEquiv
  exact e.symm.trans (e1 ≪≫ e2 ≪≫ e3).toLinearEquiv

/-- ## 概要
固定基底上の I 完全忠実平坦な代数の有向余極限は I 完全忠実平坦。
BS Thm 7.14（著者版 p.61）の極限段の通常余極限について、完全忠実平坦性を保存する。

## 方針
完全平坦性の余極限保存と、通常剰余代数の忠実平坦性の余極限保存を、
剰余テンソルの R/I 線形比較で結ぶ。

## 規約
環と添字は Type u。I は任意。p 正則性・単射性・Noether 性は要求しない。
p 進完備化による保存はこの定理の結論に含めない。

## 使われ方
超限塔の極限段で、完備化前の環の完全忠実平坦性を供給する。
-/
theorem isCompletelyFaithfullyFlat_algebraDirectLimit
    (hS : ∀ i, IsCompletelyFaithfullyFlat I (S i)) :
    IsCompletelyFaithfullyFlat I (_root_.DirectLimit S f) := by
  refine ⟨SerrePositivity.BhattScholze.Andre.Transfinite.isCompletelyFlat_algebraDirectLimit
    I S f (fun i ↦ (hS i).1), ?_⟩
  let B := fun i ↦ S i ⧸ I.map (algebraMap A (S i))
  let g := residueTransition S f I
  have hB (i : ι) : Module.FaithfullyFlat (A ⧸ I) (B i) := by
    have := (hS i).2
    exact Module.FaithfullyFlat.of_linearEquiv (A ⧸ I) ((A ⧸ I) ⊗[A] S i)
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (S i) I).toLinearEquiv
  have := SerrePositivity.BhattScholze.Andre.Transfinite.faithfullyFlat_algebraDirectLimit B g hB
  exact Module.FaithfullyFlat.of_linearEquiv (A ⧸ I) (_root_.DirectLimit B g)
    (residueTensorDirectLimitEquiv S f I)
end SerrePositivity.BhattScholze.Andre.Transfinite
