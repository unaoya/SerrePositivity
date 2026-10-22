module

public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestriction

/-!
概要：双加群の三射の合成と、その underlying 射の式を分離して公開する。
方針：一般のモノイダル圏上で合成を計算し、具体的な作用の展開を避ける。
規約：元の三射を保持。使われ方：零底と元の底の係数比較。
-/

@[expose] public section
universe u v
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {A B : Mon C} {M N P Q : Bimod A B}

def bimoduleComposition (a : M ⟶ N) (b : N ⟶ P) (c : P ⟶ Q) : M ⟶ Q :=
  a ≫ b ≫ c

lemma bimoduleComposition_hom (a : M ⟶ N) (b : N ⟶ P) (c : P ⟶ Q) :
    (bimoduleComposition a b c).hom = a.hom ≫ b.hom ≫ c.hom := rfl

end SerrePositivity.KST.LocalizingInvariants
