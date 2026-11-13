module
public import SerrePositivity.KST.SConstruction.Cofinality.WideBiproductEdges

/-!
概要：同じ全多次数の元の wide 成分に双積の和を定める。
方針：両変数の辺不変性で成分集合へ降ろし、双積同型から演算法則を得る。
規約：演算は元の指定完備化射の wide 成分に定める。
使われ方：離散的障害と K₀ 余核の群としての比較。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の wide 成分上の双積による和。
方針：両変数の実辺の関係で不変な対象の双積を二回降ろす。
規約：代表頂点の選択に依存しない。
使われ方：障害の離散成分の加法演算。 -/
def completionWideAdd (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    SSet.π₀ (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val : SSet.{u}) →
      SSet.π₀ (LocalizingInvariants.completionCofiberWide
        (((multiSEndofunctor r).obj ι).map f).val : SSet.{u}) →
        SSet.π₀ (LocalizingInvariants.completionCofiberWide
          (((multiSEndofunctor r).obj ι).map f).val : SSet.{u}) :=
  SSet.π₀.lift (fun x => SSet.π₀.lift (fun y => completionWideObjectClass r ι f hf
      ((HomotopyCategory.mk x.val : hoFunctor.obj
        (((multiSEndofunctor r).obj ι).obj Y).carrier) ⊞ HomotopyCategory.mk y.val))
    (by
      intro y z a
      exact completionWideObjectClass_biprod_edge_right r ι f hf a
        (HomotopyCategory.mk x.val))) (by
      intro x y a
      funext q
      obtain ⟨z, rfl⟩ := SSet.π₀.mk_surjective q
      exact completionWideObjectClass_biprod_edge_left r ι f hf a
        (HomotopyCategory.mk z.val))

/-- 概要：和は元のホモトピー圏の対象表示で双積を回収する。
方針：両対象を実頂点表示に戻して降下の定義を計算する。
規約：同じ指定射の成分値を使う。
使われ方：双積の同型からの演算法則の輸送。 -/
lemma completionWideAdd_objectClass (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (a b : hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier) :
    completionWideAdd r ι f hf (completionWideObjectClass r ι f hf a)
      (completionWideObjectClass r ι f hf b) = completionWideObjectClass r ι f hf (a ⊞ b) := by
  obtain ⟨a, rfl⟩ := Truncated.HomotopyCategory.mk_surjective a
  obtain ⟨b, rfl⟩ := Truncated.HomotopyCategory.mk_surjective b
  rfl

/-- 概要：元の零対象は wide 成分の和の単位候補を与える。
方針：同じ標的の選択した零頂点の成分を取る。
規約：元の未置換の頂点を保持する。
使われ方：離散的障害の零元。 -/
def completionWideZero (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    SSet.π₀ (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val : SSet.{u}) :=
  completionWideObjectClass r ι f hf
    (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex (((multiSEndofunctor r).obj ι).obj Y).carrier).vertex)

/-- 概要：成分の双積和は可換。
方針：元の双積の交換同型を成分の等号へ写す。
規約：全成分で成り立つ。
使われ方：障害成分の可換群構造。 -/
lemma completionWideAdd_comm (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (a b : SSet.π₀ (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val : SSet.{u})) :
    completionWideAdd r ι f hf a b = completionWideAdd r ι f hf b a := by
  obtain ⟨a, rfl⟩ := SSet.π₀.mk_surjective a
  obtain ⟨b, rfl⟩ := SSet.π₀.mk_surjective b
  exact completionWideObjectClass_iso r ι f hf (biprod.braiding
    (C := hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier)
    (HomotopyCategory.mk a.val : hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier)
    (HomotopyCategory.mk b.val))

/-- 概要：成分の双積和は結合的。
方針：対象表示で和を計算し、元の双積の結合同型を使う。
規約：全成分の三つ組を扱う。
使われ方：障害成分の可換群構造。 -/
lemma completionWideAdd_assoc (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (a b c : SSet.π₀ (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val : SSet.{u})) :
    completionWideAdd r ι f hf (completionWideAdd r ι f hf a b) c =
      completionWideAdd r ι f hf a (completionWideAdd r ι f hf b c) := by
  obtain ⟨a, rfl⟩ := SSet.π₀.mk_surjective a
  obtain ⟨b, rfl⟩ := SSet.π₀.mk_surjective b
  obtain ⟨c, rfl⟩ := SSet.π₀.mk_surjective c
  change completionWideAdd r ι f hf
      (completionWideObjectClass r ι f hf (HomotopyCategory.mk a.val ⊞
        (HomotopyCategory.mk b.val : hoFunctor.obj
          (((multiSEndofunctor r).obj ι).obj Y).carrier)))
      (completionWideObjectClass r ι f hf (HomotopyCategory.mk c.val)) = _
  rw [completionWideAdd_objectClass]
  change _ = completionWideAdd r ι f hf
    (completionWideObjectClass r ι f hf (HomotopyCategory.mk a.val))
    (completionWideObjectClass r ι f hf ((HomotopyCategory.mk b.val : hoFunctor.obj
      (((multiSEndofunctor r).obj ι).obj Y).carrier) ⊞ HomotopyCategory.mk c.val))
  rw [completionWideAdd_objectClass]
  exact completionWideObjectClass_iso r ι f hf (biprod.associator _ _ _)

/-- 概要：元の零成分は双積和の左単位。
方針：零対象と任意の対象の双積の標準同型を成分へ写す。
規約：選択された零頂点の零性だけを使う。
使われ方：障害成分の加法単位の検証。 -/
lemma completionWideAdd_zero_left (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (a : SSet.π₀ (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val : SSet.{u})) :
    completionWideAdd r ι f hf (completionWideZero r ι f hf) a = a := by
  obtain ⟨a, rfl⟩ := SSet.π₀.mk_surjective a
  let z := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex (((multiSEndofunctor r).obj ι).obj Y).carrier
  exact (completionWideAdd_objectClass r ι f hf (HomotopyCategory.mk z.vertex)
    (HomotopyCategory.mk a.val)).trans
      (completionWideObjectClass_iso r ι f hf (isoZeroBiprod
        (C := hoFunctor.obj (((multiSEndofunctor r).obj ι).obj Y).carrier)
        (Y := (HomotopyCategory.mk a.val : hoFunctor.obj
          (((multiSEndofunctor r).obj ι).obj Y).carrier)) z.isZero.isZeroHo).symm)

/-- 概要：元の零成分は双積和の右単位。
方針：可換性と左単位則を合成する。
規約：全成分で成り立つ。
使われ方：障害成分の加法単位の検証。 -/
lemma completionWideAdd_zero_right (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (a : SSet.π₀ (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val : SSet.{u})) :
    completionWideAdd r ι f hf a (completionWideZero r ι f hf) = a :=
  (completionWideAdd_comm r ι f hf a _).trans (completionWideAdd_zero_left r ι f hf a)

end SerrePositivity.KST.SConstruction.Cofinality
