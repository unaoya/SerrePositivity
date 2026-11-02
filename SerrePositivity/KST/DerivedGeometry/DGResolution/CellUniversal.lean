module

public import SerrePositivity.KST.DerivedGeometry.DGResolution.CellEmbedding
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Path

/-!
# 指定微分を持つ自由な生成元添加の普遍性

概要：添加した dg 圏からの関手を、前段階の関手と生成元の像の組で分類する。
方針：有限語の評価による延長と、生成元への制限の往復を証明する。
規約：追加する像の微分は指定境界と一致する。閉元とは限らない。
使われ方：Drinfeld §13.4・Lemma 13.5 の半自由な添加。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z

namespace SerrePositivity.KST.DerivedGeometry.DGResolution

open CategoryTheory
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : DGCellAttachment.Family A D I)
  (E : Type z) [DGCategory A E]

/--
概要：添加前の関手と、指定微分を満たす生成元の像からなるデータ。
方針：既存の具体的な原始元のデータを従属和にまとめる。
規約：分解の存在や平坦性の証明を入力には要求しない。
使われ方：Drinfeld §13.4・Lemma 13.5 の自由添加の普遍性。
-/
abbrev CellExtensionData :=
  Σ F : DGFunctor A D E, DGCellAttachment.Family.PrimitiveData A D I C E F

/--
概要：関手と生成元の像を指定すると、添加した圏からの延長関手は一意に定まる。
方針：元の関手への制限と各生成元の像を計算して単射性を示す。
規約：全ての有限語の像は合成から決まる。
使われ方：Drinfeld §13.4・Lemma 13.5 の自由な生成元添加。
-/
theorem cellExtension_injective : Function.Injective
    (fun p : CellExtensionData A D I C E => p.2.extension) := by
  let restrict : DGFunctor A (C.Objects A D I) E → CellExtensionData A D I C E :=
    fun G => ⟨C.restrictFunctor A D I G, C.restrictPrimitives A D I G⟩
  have recover (p : CellExtensionData A D I C E) : restrict p.2.extension = p := by
    rcases p with ⟨F, P⟩
    apply Sigma.ext P.embedding_comp_extension
    exact (C.restrictPrimitives A D I P.extension).hext P P.embedding_comp_extension
      (heq_of_eq (funext P.extension_generator))
  intro p q h
  exact (recover p).symm.trans ((congrArg restrict h).trans (recover q))

/--
概要：添加した圏からの任意の dg 関手は、元の関手と生成元の像から再構成できる。
方針：包含へ制限し、各生成元の像を原始元として有限語を再評価する。
規約：関手の追加条件は要求しない。
使われ方：Drinfeld §13.4・Lemma 13.5 の自由な生成元添加。
-/
theorem cellExtension_surjective : Function.Surjective
    (fun p : CellExtensionData A D I C E => p.2.extension) := by
  intro G
  exact ⟨⟨C.restrictFunctor A D I G, C.restrictPrimitives A D I G⟩,
    C.extension_restrict A D I G⟩

/--
概要：添加した圏からの dg 関手と、添加前の関手および生成元の像は全単射に対応する。
方針：有限語での評価の延長が単射・全射であることをまとめる。
規約：指定境界の条件は実際の原始元のデータに含まれ、証明済みの延長を使う。
使われ方：Drinfeld §13.4・Lemma 13.5 の一段の半自由拡張。
-/
def cellFunctorEquiv :
    DGFunctor A (C.Objects A D I) E ≃ CellExtensionData A D I C E :=
  (Equiv.ofBijective (fun p : CellExtensionData A D I C E => p.2.extension)
    ⟨cellExtension_injective A D I C E, cellExtension_surjective A D I C E⟩).symm

/--
概要：自由添加の普遍性の順写像は実際の包含への制限と生成元への評価。
方針：延長の単射性と制限後の再構成を使う。
規約：存在だけの逆写像にせず、具体的な制限との一致を示す。
使われ方：Drinfeld §13.4・Lemma 13.5 の段階ごとの比較。
-/
theorem cellFunctorEquiv_apply (G : DGFunctor A (C.Objects A D I) E) :
    cellFunctorEquiv A D I C E G =
      ⟨C.restrictFunctor A D I G, C.restrictPrimitives A D I G⟩ := by
  apply (cellFunctorEquiv A D I C E).symm.injective
  change (cellFunctorEquiv A D I C E).symm (cellFunctorEquiv A D I C E G) =
    (C.restrictPrimitives A D I G).extension
  rw [Equiv.symm_apply_apply, C.extension_restrict A D I G]

end SerrePositivity.KST.DerivedGeometry.DGResolution
