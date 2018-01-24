- You will need the master branch of agda:

   git clone http://github.com/agda/agda
   cd agda
   cabal install

- The standard library.

- And the cubical library
   git clone https://github.com/Saizan/cubical-demo
   -- also make sure the path to cubical-demo/cubical.agda-lib is in your ~/.agda/libraries



- Prove composition law for Maybe functor and MaybeT (Reader r)
  -- see Functor file

- Implement the absoulte value and sign functions, then prove you can
  reconstruct an Int from those.
  -- see Abs file

- Implementing Basic Operations

  - Using J
    - implement sym and trans for path from pathJ
    - prove trans p refl ≡ p with pathJ and pathJprop

  - Using Comp (i.e. closing boxes)
    - implement again trans and trans-id but using primComp this time.

  -- see JandComp file

- Show that you can get a monoid iso from an equality in monoid type,
     i.e. sends unit to unit and mult to mult.
  -- see Monoid file.

- Paths also give a good notion of equality for coinductive structures.
  - prove the map-id and eta laws for streams
  -- see Stream file.