module

public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Sifted
public import Mathlib.CategoryTheory.Limits.Connected

/-!
# dg 代数の単位・二項積・結合則の入力関手

概要：底の sifted 余極限を単位と二重・三重テンソルが保存する。
方針：各変数の閉随伴による保存と対角の final 性を組み合わせる。
規約：一般の余極限の保存を主張しない。
使われ方：モノイド構造を底の余極限へ降ろす。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DGAlgebra
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded
variable {R : Type u} [CommRing R]

/-- 概要：単位演算の定数入力関手。
方針：単位複体の定値関手。
規約：元の複体圏上の自己関手。
使われ方：単位の余極限への降下。 -/
abbrev unitInput : Complex R ⥤ Complex R := (Functor.const _).obj (𝟙_ (Complex R))

/-- 概要：二項積の対角テンソル入力。
方針：恒等関手二つの点ごとのテンソル。
規約：X ⊗ X を厳密に使う。
使われ方：積の余極限への降下。 -/
abbrev binaryInput : Complex R ⥤ Complex R := (𝟭 (Complex R)) ⊗ (𝟭 (Complex R))

/-- 概要：結合則の左に括った三重入力。
方針：二重入力の右へ恒等関手をテンソルする。
規約：(X ⊗ X) ⊗ X の括りを固定する。
使われ方：降りた積の結合則の検証。 -/
abbrev ternaryInput : Complex R ⥤ Complex R := _root_.SerrePositivity.DGAlgebra.binaryInput ⊗ (𝟭 (Complex R))

/-- 概要：保存する二関手の点ごとのテンソルも sifted 余極限を保存する。
方針：二変数の普遍性を final な対角へ制限する。
規約：保存は指定した図式についてのみ要求する。
使われ方：二重・三重入力の保存。 -/
lemma tensorInput_preservesColimit {J : Type w} [Category.{v} J] [IsSifted J]
    (H : J ⥤ Complex R) (F G : Complex R ⥤ Complex R)
    [PreservesColimit H F] [PreservesColimit H G] : PreservesColimit H (F ⊗ G) := by
  refine ⟨fun {c} hc => ?_⟩
  have h₂ := isColimitOfPreserves₂ (curriedTensor (Complex R))
    (isColimitOfPreserves F hc) (isColimitOfPreserves G hc)
  have hd := (Functor.Final.isColimitWhiskerEquiv (Functor.diag J) _).symm h₂
  let d := ((curriedTensor (Complex R)).mapCocone₂ (F.mapCocone c) (G.mapCocone c)).whisker
    (Functor.diag J)
  let e : Functor.diag J ⋙ Functor.uncurry.obj
      ((((Functor.whiskeringLeft₂ (Complex R)).obj (H ⋙ F)).obj (H ⋙ G)).obj
        (curriedTensor (Complex R))) ≅ H ⋙ (F ⊗ G) :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by intro i j f; simp [tensorHom_def])
  exact ⟨(IsColimit.equivOfNatIsoOfIso e d ((F ⊗ G).mapCocone c)
    (Cocone.ext (Iso.refl _) (by intro j; simp [d, e, tensorHom_def]))).toFun hd⟩

/-- 概要：単位の定値入力は連結な余極限を保存する。
方針：定値余錐の連結な形での普遍性。
規約：図式ごとの保存だけを述べる。
使われ方：sifted 余極限での単位の降下。 -/
lemma unitInput_preservesColimit {J : Type w} [Category.{v} J] [IsConnected J]
    (H : J ⥤ Complex R) : PreservesColimit H _root_.SerrePositivity.DGAlgebra.unitInput := by
  refine ⟨fun {c} _ => ?_⟩
  exact ⟨isColimitConstCocone J (𝟙_ (Complex R))⟩

end SerrePositivity.DGAlgebra
