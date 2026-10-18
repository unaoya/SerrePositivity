module

public import SerrePositivity.KST.DerivedGeometry.DGResolution.Construction

/-!
# 生成元添加の次数別分裂単射

概要：半自由な生成元添加で、前段階の Hom が次数ごとに分裂して含まれることを示す。
方針：有限語の直和から空語成分へ射影する。
規約：射影は内部微分についてのみ chain map。添加後の微分との可換性は主張しない。
使われ方：Drinfeld §13.4・Lemma 13.5、KST D4 の半自由な段階表示。
-/

@[expose] public section
noncomputable section
universe u v w

namespace SerrePositivity.KST.DerivedGeometry.DGResolution

open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (I : Type w) [Small.{u} I] (C : DGCellAttachment.Family A D I)

/--
概要：有限語の内部複体の直和から空語成分への射影。
方針：非空語を零へ送り、空語では恒等射を使う。
規約：添加後の Hom からの chain map とはしない。
使われ方：Drinfeld §13.4・Lemma 13.5 の次数別分裂。
-/
def emptyWordProjection (x y : D) : C.internalHom A D I x y ⟶ homObject A D x y :=
  Sigma.desc fun w => match w with
    | [] => 𝟙 _
    | _ :: _ => 0

/--
概要：空語の包含と空語射影の合成は恒等射。
方針：直和の包含と降下の計算を使う。
規約：この式は内部微分の複体での式。
使われ方：Drinfeld Lemma 13.5 の生成元添加の分裂。
-/
lemma originalHom_emptyWordProjection (x y : D) :
    C.originalHom A D I x y ≫ emptyWordProjection A D I C x y = 𝟙 _ :=
  Sigma.ι_comp_desc _ _

/--
概要：添加後の Hom への包含は各次数で空語射影を左逆に持つ。
方針：包含の次数成分が内部複体の空語包含と同じことを使う。
規約：射影が添加後の微分と可換であるとは主張しない。
使われ方：Drinfeld §13.4・Lemma 13.5 の半自由フィルトレーション。
-/
lemma attachment_degree_retraction (x y : D) (n : ℤ) :
    (C.originalHomInclusion A D I x y).f n ≫ (emptyWordProjection A D I C x y).f n = 𝟙 _ :=
  congrArg (fun f => f.f n) (originalHom_emptyWordProjection A D I C x y)

/--
概要：生成元添加の包含は次数ごとに分裂単射。
方針：空語射影を次数ごとの左逆として登録する。
規約：複体の分裂ではなく加群の分裂を示す。
使われ方：Drinfeld §13.4・Lemma 13.5 の段階列の単射性。
-/
instance attachment_degree_splitMono (x y : D) (n : ℤ) :
    IsSplitMono ((C.originalHomInclusion A D I x y).f n) :=
  ⟨⟨⟨(emptyWordProjection A D I C x y).f n,
    attachment_degree_retraction A D I C x y n⟩⟩⟩

/--
概要：生成元添加の包含は複体の圏で単射。
方針：各次数の分裂単射性から単射性を得る。
規約：複体の圏で分裂するとは主張しない。
使われ方：Drinfeld Lemma 13.5 の増大列の包含。
-/
instance attachment_mono (x y : D) : Mono (C.originalHomInclusion A D I x y) :=
  HomologicalComplex.mono_of_mono_f _ fun _ => inferInstance

end SerrePositivity.KST.DerivedGeometry.DGResolution
