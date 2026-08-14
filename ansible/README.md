# LastLib host setup

This playbook turns a fresh Ubuntu 26.04 server into the environment reconstructed
from the machine's initial root Bash and `phulin` Fish histories. It:

- installs Fish, tmux, Git, build tools, FUSE/`fuse-overlayfs`, ripgrep, and the
  other packages used by LastLib;
- creates `phulin`, puts it in `sudo`, selects Fish, and installs the observed
  public SSH key;
- clones and links the dotfiles;
- persists the file-table, pipe-page, inotify, and per-user open-file limits used
  for large swarm runs;
- clones the `book1-lean` branch using an HTTPS URL that contains no credential;
  and
- runs `scripts/setup_ubuntu.sh` once, installing uv, Python, elan, Lean, Codex,
  dependencies, and the Mathlib executable cache.

The history also contained a GitHub personal access token inside a clone URL.
That token is deliberately absent from this repository and should be revoked.
The playbook can read a replacement from a protected file on the controller and
uses it only as a transient Git authentication header. It is not placed in the
command line, target filesystem, Git remote, or Ansible output.

## Controller setup

Install Ansible on your laptop or other controller. On Ubuntu:

```console
sudo apt update
sudo apt install ansible
```

Store a GitHub PAT once. The prompt does not echo the token, and the helper
creates both the directory and file with owner-only permissions:

```console
./ansible/store-github-pat
```

A fine-grained replacement token only needs read access to this repository's
contents. The token copied from shell history should be treated as compromised
even if it still works.

The default path is `~/.config/lastlib/github.pat`. Keep the laptop's disk
encrypted and do not synchronize or commit this file. To keep it elsewhere,
export `LASTLIB_GITHUB_PAT_FILE=/path/to/github.pat` before running either helper.

Provision a new server with one command:

```console
./ansible/bootstrap 203.0.113.10
```

The wrapper uses an inline inventory, accepts a new host key on first contact,
and assumes the fresh server accepts SSH as `root`. If your provider uses an
initial account such as `ubuntu`, select it without editing files:

```console
LASTLIB_SSH_USER=ubuntu ./ansible/bootstrap 203.0.113.10
```

Ansible will use `sudo` because the play has `become: true`. Add
`--ask-pass` if the initial SSH login uses a password, and add
`--ask-become-pass` if the initial non-root account requires a sudo password.

## Inventory-based usage

The wrapper is the shortest route, but a conventional inventory is included for
repeated use. Copy it, then replace the documentation-only IP address:

```console
cp ansible/inventory.example.ini ansible/inventory.ini
$EDITOR ansible/inventory.ini
```

Check connectivity and preview the changes:

```console
ansible -i ansible/inventory.ini lastlib -m ping
ansible-playbook -i ansible/inventory.ini ansible/setup.yml --check --diff
```

Apply them:

```console
ansible-playbook -i ansible/inventory.ini ansible/setup.yml
```

The project bootstrap downloads toolchains, dependencies, and the Mathlib cache,
so it can still take some time. To provision only the account, packages,
repositories, dotfiles, and host limits, run:

```console
ansible-playbook -i ansible/inventory.ini ansible/setup.yml \
  -e lastlib_run_project_setup=false
```

The same override works with the one-command wrapper:

```console
./ansible/bootstrap 203.0.113.10 -e lastlib_run_project_setup=false
```

Afterward, start a new login so Fish and the limits are active:

```console
ssh phulin@YOUR_SERVER
ulimit -Sn
tmux
cd ~/LastLib
uv run lastlib-swarm plan books/
```

The playbook grants passwordless sudo to the SSH-key-authenticated `phulin`
account so the repository bootstrap can install packages unattended. If that is
not appropriate for the server's security model, replace the generated
`/etc/sudoers.d/90-phulin` rule and configure a password or narrower sudo policy
before exposing the host.

The `.ansible-bootstrap-complete` marker prevents the expensive project setup
from running again. Remove only that marker and rerun the playbook when you
intentionally want the full bootstrap repeated.
