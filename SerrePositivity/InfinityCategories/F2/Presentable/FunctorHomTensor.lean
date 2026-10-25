module

public import SerrePositivity.InfinityCategories.F2.Presentable.FunctorTensorIso
public import SerrePositivity.InfinityCategories.F2.Presentable.FunctorHomWhiskering
public import SerrePositivity.InfinityCategories.F2.CatInfinity.QCatTensorAndArrowObjects

/-!
概要：直積値の全関手間の二胞体を、元の二つの成分の二胞体へ分解する。
方針：全関手圏の積同型とホモトピー圏の積比較を合成する。
規約：任意の全パラメーターを保持し、各点の Hom 集合だけには制限しない。
使われ方：二つの既存の全随伴から直積の全随伴を組み立てる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：直積値の全関手間の h Fun の射は元の二つの成分の射と全単射。
方針：元の全関手圏の同型とホモトピー圏の積同値の充満忠実性を使う。
規約：両端 F・G を固定して全二胞体を比較する。
使われ方：直積の随伴 Hom 対応。 -/
def functorHomTensorEquiv {T X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (F G : T ⟶ X ⊗ Y) :
    FunctorHom F G ≃
      (FunctorHom (F ≫ fst X Y) (G ≫ fst X Y) ×
        FunctorHom (F ≫ snd X Y) (G ≫ snd X Y)) := by
  have : Quasicategory (X ⊗ Y) := F2.quasicategory_tensor X Y
  have : Quasicategory ((ihom T).obj X ⊗ (ihom T).obj Y) :=
    F2.quasicategory_tensor _ _
  let e := functorTensorIso T X Y
  have hf := (qCatEquivalenceOfIso e).isQCatEquivalence.isFullyFaithful.toHoFullyFaithful
  let b := Truncated.HomotopyCategory.BinaryProduct.equivalence
    ((truncation 2).obj ((ihom T).obj X)) ((truncation 2).obj ((ihom T).obj Y))
  exact (hf.comp b.fullyFaithfulFunctor).homEquiv

/-- 概要：全単射の順方向は二つの元の射影による後合成そのもの。
方針：積比較の二つの脚とホモトピー圏への合成の作用を照合する。
規約：二胞体 α の代表を選び直さない。
使われ方：成分ごとの自然性を全パラメーターへ戻す。 -/
lemma functorHomTensorEquiv_apply {T X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F G : T ⟶ X ⊗ Y} (α : FunctorHom F G) :
    functorHomTensorEquiv F G α =
      ((hoFunctor.map ((ihom T).map (fst X Y))).toFunctor.map α,
        (hoFunctor.map ((ihom T).map (snd X Y))).toFunctor.map α) := by
  have : Quasicategory (X ⊗ Y) := F2.quasicategory_tensor X Y
  obtain ⟨e, rfl⟩ := homotopyCategory_homMk_surjective _ _ α
  rfl

/-- 概要：二胞体の直積分解は合成と可換。
方針：二つの元の後合成関手の合成保存を使う。
規約：元の三つの全関手を保持する。
使われ方：直積の随伴 Hom 対応の自然性。 -/
lemma functorHomTensorEquiv_comp {T X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F G H : T ⟶ X ⊗ Y} (α : FunctorHom F G) (β : FunctorHom G H) :
    functorHomTensorEquiv F H (α ≫ β) =
      ((functorHomTensorEquiv F G α).1 ≫ (functorHomTensorEquiv G H β).1,
        (functorHomTensorEquiv F G α).2 ≫ (functorHomTensorEquiv G H β).2) := by
  simp only [functorHomTensorEquiv_apply, CategoryTheory.Functor.map_comp]

/-- 概要：全パラメーターの制限は二胞体の直積分解と可換。
方針：元の前合成と射影への後合成の可換性を使う。
規約：パラメーターの充填性を要求しない。
使われ方：直積の随伴 Hom 対応のパラメーター自然性。 -/
lemma functorHomTensorEquiv_precomp {A T X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (i : A ⟶ T)
    {F G : T ⟶ X ⊗ Y} (α : FunctorHom F G) :
    functorHomTensorEquiv (i ≫ F) (i ≫ G)
      ((hoFunctor.map ((pre i).app (X ⊗ Y))).toFunctor.map α) =
      ((hoFunctor.map ((pre i).app X)).toFunctor.map (functorHomTensorEquiv F G α).1,
        (hoFunctor.map ((pre i).app Y)).toFunctor.map (functorHomTensorEquiv F G α).2) := by
  simp only [functorHomTensorEquiv_apply, ← functorHom_pre_post]

/-- 概要：二関手の直積による後合成は二胞体の成分分解と可換。
方針：元の二胞体の実辺代表で二つの射影の作用を計算する。
規約：比較は元の全パラメーター上で行う。
使われ方：積の単位による Hom 比較の分解。 -/
lemma functorHomTensorEquiv_postcomp {T X Y X' Y' : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory X'] [Quasicategory Y']
    (f : X ⟶ X') (g : Y ⟶ Y') {F G : T ⟶ X ⊗ Y} (α : FunctorHom F G) :
    functorHomTensorEquiv (F ≫ (f ⊗ₘ g)) (G ≫ (f ⊗ₘ g))
      ((hoFunctor.map ((ihom T).map (f ⊗ₘ g))).toFunctor.map α) =
      ((hoFunctor.map ((ihom T).map f)).toFunctor.map (functorHomTensorEquiv F G α).1,
        (hoFunctor.map ((ihom T).map g)).toFunctor.map (functorHomTensorEquiv F G α).2) := by
  have : Quasicategory (X ⊗ Y) := F2.quasicategory_tensor X Y
  simp only [functorHomTensorEquiv_apply]
  obtain ⟨e, rfl⟩ := homotopyCategory_homMk_surjective _ _ α
  rfl

end SerrePositivity.InfinityCategories.F2.Presentable
